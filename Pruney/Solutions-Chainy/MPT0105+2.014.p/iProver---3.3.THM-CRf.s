%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:13 EST 2020

% Result     : Theorem 8.06s
% Output     : CNFRefutation 8.06s
% Verified   : 
% Statistics : Number of formulae       :  116 (2223 expanded)
%              Number of clauses        :   76 ( 816 expanded)
%              Number of leaves         :   14 ( 601 expanded)
%              Depth                    :   24
%              Number of atoms          :  128 (2499 expanded)
%              Number of equality atoms :  118 (2273 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f13,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f34,f36,f36,f30])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f30,f30])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f31,f30,f30])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f14,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f14])).

fof(f19,plain,(
    ? [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f15])).

fof(f20,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_xboole_0(X0,X1)
   => k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f35,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) != k2_xboole_0(sK0,sK1) ),
    inference(definition_unfolding,[],[f35,f36])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_0,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_112,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_0,c_5])).

cnf(c_113,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))))))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_112,c_5])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_538,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_559,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_538,c_4,c_6])).

cnf(c_601,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_559,c_5])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_84,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1089,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_559,c_84])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_83,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1619,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1089,c_83])).

cnf(c_3575,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_113,c_4,c_601,c_1619])).

cnf(c_3620,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_3575])).

cnf(c_1087,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_84])).

cnf(c_1201,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1087,c_83])).

cnf(c_3713,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X0) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_3620,c_4,c_1201])).

cnf(c_3943,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3713,c_6])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_394,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_12751,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X1),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X1),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3943,c_394])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_106,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_8,c_5])).

cnf(c_9,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_89,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_9,c_4])).

cnf(c_594,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_559,c_89])).

cnf(c_843,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_594,c_4])).

cnf(c_13361,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X0)),k2_xboole_0(X1,X1))) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X1,X1)) ),
    inference(demodulation,[status(thm)],[c_12751,c_5,c_106,c_843])).

cnf(c_2103,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_559,c_106])).

cnf(c_2166,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2103,c_4,c_559])).

cnf(c_1091,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_601,c_84])).

cnf(c_1754,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1091])).

cnf(c_7654,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2166,c_1754])).

cnf(c_7690,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7654,c_843])).

cnf(c_7897,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_7690])).

cnf(c_8271,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_7897])).

cnf(c_530,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_8315,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8271,c_530])).

cnf(c_8349,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_8315,c_83])).

cnf(c_397,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_8584,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8349,c_397])).

cnf(c_13362,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X0)) = k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_13361,c_8584])).

cnf(c_385,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_5])).

cnf(c_718,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_385,c_559])).

cnf(c_939,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_718,c_1])).

cnf(c_946,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_939,c_4,c_385])).

cnf(c_947,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_946,c_4,c_559])).

cnf(c_13363,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X1)) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(demodulation,[status(thm)],[c_13362,c_947,c_1619])).

cnf(c_13364,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_13363,c_1619])).

cnf(c_15831,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_13364,c_3713])).

cnf(c_1440,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_397,c_84])).

cnf(c_8583,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8349,c_1440])).

cnf(c_10813,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_8583,c_83])).

cnf(c_15171,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1)))) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10813,c_3575])).

cnf(c_15266,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1)))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_15171,c_10813])).

cnf(c_15268,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_15266,c_4,c_530,c_8584])).

cnf(c_7656,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X0),k2_xboole_0(X1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3943,c_1754])).

cnf(c_7684,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X0)),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7656,c_5,c_843])).

cnf(c_7685,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7684,c_1619])).

cnf(c_7813,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = X1 ),
    inference(superposition,[status(thm)],[c_7685,c_83])).

cnf(c_383,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_8697,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_7813,c_383])).

cnf(c_9217,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_8697,c_4,c_6])).

cnf(c_15269,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_15268,c_9217])).

cnf(c_18325,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_15831,c_15269])).

cnf(c_19014,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_18325,c_15831])).

cnf(c_11,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) != k2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_109,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_11,c_106])).

cnf(c_8525,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_8349,c_109])).

cnf(c_8526,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_8525,c_4,c_559])).

cnf(c_25548,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_19014,c_8526])).

cnf(c_25555,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_25548])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.06/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.06/1.51  
% 8.06/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.06/1.51  
% 8.06/1.51  ------  iProver source info
% 8.06/1.51  
% 8.06/1.51  git: date: 2020-06-30 10:37:57 +0100
% 8.06/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.06/1.51  git: non_committed_changes: false
% 8.06/1.51  git: last_make_outside_of_git: false
% 8.06/1.51  
% 8.06/1.51  ------ 
% 8.06/1.51  ------ Parsing...
% 8.06/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.06/1.51  
% 8.06/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 8.06/1.51  
% 8.06/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.06/1.51  
% 8.06/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.06/1.51  ------ Proving...
% 8.06/1.51  ------ Problem Properties 
% 8.06/1.51  
% 8.06/1.51  
% 8.06/1.51  clauses                                 12
% 8.06/1.51  conjectures                             1
% 8.06/1.51  EPR                                     0
% 8.06/1.51  Horn                                    12
% 8.06/1.51  unary                                   10
% 8.06/1.51  binary                                  2
% 8.06/1.51  lits                                    14
% 8.06/1.51  lits eq                                 12
% 8.06/1.51  fd_pure                                 0
% 8.06/1.51  fd_pseudo                               0
% 8.06/1.51  fd_cond                                 0
% 8.06/1.51  fd_pseudo_cond                          0
% 8.06/1.51  AC symbols                              0
% 8.06/1.51  
% 8.06/1.51  ------ Input Options Time Limit: Unbounded
% 8.06/1.51  
% 8.06/1.51  
% 8.06/1.51  ------ 
% 8.06/1.51  Current options:
% 8.06/1.51  ------ 
% 8.06/1.51  
% 8.06/1.51  
% 8.06/1.51  
% 8.06/1.51  
% 8.06/1.51  ------ Proving...
% 8.06/1.51  
% 8.06/1.51  
% 8.06/1.51  % SZS status Theorem for theBenchmark.p
% 8.06/1.51  
% 8.06/1.51   Resolution empty clause
% 8.06/1.51  
% 8.06/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 8.06/1.51  
% 8.06/1.51  fof(f7,axiom,(
% 8.06/1.51    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 8.06/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.06/1.51  
% 8.06/1.51  fof(f28,plain,(
% 8.06/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 8.06/1.51    inference(cnf_transformation,[],[f7])).
% 8.06/1.51  
% 8.06/1.51  fof(f13,axiom,(
% 8.06/1.51    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 8.06/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.06/1.51  
% 8.06/1.51  fof(f34,plain,(
% 8.06/1.51    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 8.06/1.51    inference(cnf_transformation,[],[f13])).
% 8.06/1.51  
% 8.06/1.51  fof(f3,axiom,(
% 8.06/1.51    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 8.06/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.06/1.51  
% 8.06/1.51  fof(f24,plain,(
% 8.06/1.51    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)) )),
% 8.06/1.51    inference(cnf_transformation,[],[f3])).
% 8.06/1.51  
% 8.06/1.51  fof(f36,plain,(
% 8.06/1.51    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1)) )),
% 8.06/1.51    inference(definition_unfolding,[],[f24,f30])).
% 8.06/1.51  
% 8.06/1.51  fof(f9,axiom,(
% 8.06/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 8.06/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.06/1.51  
% 8.06/1.51  fof(f30,plain,(
% 8.06/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.06/1.51    inference(cnf_transformation,[],[f9])).
% 8.06/1.51  
% 8.06/1.51  fof(f37,plain,(
% 8.06/1.51    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k2_xboole_0(X0,X1)) )),
% 8.06/1.51    inference(definition_unfolding,[],[f34,f36,f36,f30])).
% 8.06/1.51  
% 8.06/1.51  fof(f6,axiom,(
% 8.06/1.51    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 8.06/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.06/1.51  
% 8.06/1.51  fof(f27,plain,(
% 8.06/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 8.06/1.51    inference(cnf_transformation,[],[f6])).
% 8.06/1.51  
% 8.06/1.51  fof(f5,axiom,(
% 8.06/1.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 8.06/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.06/1.51  
% 8.06/1.51  fof(f26,plain,(
% 8.06/1.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.06/1.51    inference(cnf_transformation,[],[f5])).
% 8.06/1.51  
% 8.06/1.51  fof(f8,axiom,(
% 8.06/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.06/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.06/1.51  
% 8.06/1.51  fof(f29,plain,(
% 8.06/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.06/1.51    inference(cnf_transformation,[],[f8])).
% 8.06/1.51  
% 8.06/1.51  fof(f39,plain,(
% 8.06/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 8.06/1.51    inference(definition_unfolding,[],[f29,f30])).
% 8.06/1.51  
% 8.06/1.51  fof(f2,axiom,(
% 8.06/1.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 8.06/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.06/1.51  
% 8.06/1.51  fof(f16,plain,(
% 8.06/1.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 => r1_tarski(X0,X1))),
% 8.06/1.51    inference(unused_predicate_definition_removal,[],[f2])).
% 8.06/1.51  
% 8.06/1.51  fof(f17,plain,(
% 8.06/1.51    ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 8.06/1.51    inference(ennf_transformation,[],[f16])).
% 8.06/1.51  
% 8.06/1.51  fof(f23,plain,(
% 8.06/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 8.06/1.51    inference(cnf_transformation,[],[f17])).
% 8.06/1.51  
% 8.06/1.51  fof(f4,axiom,(
% 8.06/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 8.06/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.06/1.51  
% 8.06/1.51  fof(f18,plain,(
% 8.06/1.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 8.06/1.51    inference(ennf_transformation,[],[f4])).
% 8.06/1.51  
% 8.06/1.51  fof(f25,plain,(
% 8.06/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 8.06/1.51    inference(cnf_transformation,[],[f18])).
% 8.06/1.51  
% 8.06/1.51  fof(f1,axiom,(
% 8.06/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 8.06/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.06/1.51  
% 8.06/1.51  fof(f22,plain,(
% 8.06/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 8.06/1.51    inference(cnf_transformation,[],[f1])).
% 8.06/1.51  
% 8.06/1.51  fof(f38,plain,(
% 8.06/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 8.06/1.51    inference(definition_unfolding,[],[f22,f30,f30])).
% 8.06/1.51  
% 8.06/1.51  fof(f10,axiom,(
% 8.06/1.51    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 8.06/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.06/1.51  
% 8.06/1.51  fof(f31,plain,(
% 8.06/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 8.06/1.51    inference(cnf_transformation,[],[f10])).
% 8.06/1.51  
% 8.06/1.51  fof(f40,plain,(
% 8.06/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 8.06/1.51    inference(definition_unfolding,[],[f31,f30,f30])).
% 8.06/1.51  
% 8.06/1.51  fof(f11,axiom,(
% 8.06/1.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 8.06/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.06/1.51  
% 8.06/1.51  fof(f32,plain,(
% 8.06/1.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.06/1.51    inference(cnf_transformation,[],[f11])).
% 8.06/1.51  
% 8.06/1.51  fof(f41,plain,(
% 8.06/1.51    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0) )),
% 8.06/1.51    inference(definition_unfolding,[],[f32,f36])).
% 8.06/1.51  
% 8.06/1.51  fof(f14,conjecture,(
% 8.06/1.51    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 8.06/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.06/1.51  
% 8.06/1.51  fof(f15,negated_conjecture,(
% 8.06/1.51    ~! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 8.06/1.51    inference(negated_conjecture,[],[f14])).
% 8.06/1.51  
% 8.06/1.51  fof(f19,plain,(
% 8.06/1.51    ? [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_xboole_0(X0,X1)),
% 8.06/1.51    inference(ennf_transformation,[],[f15])).
% 8.06/1.51  
% 8.06/1.51  fof(f20,plain,(
% 8.06/1.51    ? [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_xboole_0(X0,X1) => k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1)),
% 8.06/1.51    introduced(choice_axiom,[])).
% 8.06/1.51  
% 8.06/1.51  fof(f21,plain,(
% 8.06/1.51    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1)),
% 8.06/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 8.06/1.51  
% 8.06/1.51  fof(f35,plain,(
% 8.06/1.51    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1)),
% 8.06/1.51    inference(cnf_transformation,[],[f21])).
% 8.06/1.51  
% 8.06/1.51  fof(f43,plain,(
% 8.06/1.51    k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) != k2_xboole_0(sK0,sK1)),
% 8.06/1.51    inference(definition_unfolding,[],[f35,f36])).
% 8.06/1.51  
% 8.06/1.51  cnf(c_6,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 8.06/1.51      inference(cnf_transformation,[],[f28]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_0,plain,
% 8.06/1.51      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k2_xboole_0(X0,X1) ),
% 8.06/1.51      inference(cnf_transformation,[],[f37]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_5,plain,
% 8.06/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 8.06/1.51      inference(cnf_transformation,[],[f27]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_112,plain,
% 8.06/1.51      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k2_xboole_0(X0,X1) ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_0,c_5]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_113,plain,
% 8.06/1.51      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))))))) = k2_xboole_0(X0,X1) ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_112,c_5]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_4,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 8.06/1.51      inference(cnf_transformation,[],[f26]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_7,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 8.06/1.51      inference(cnf_transformation,[],[f39]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_538,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_559,plain,
% 8.06/1.51      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 8.06/1.51      inference(light_normalisation,[status(thm)],[c_538,c_4,c_6]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_601,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_559,c_5]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_2,plain,
% 8.06/1.51      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 8.06/1.51      inference(cnf_transformation,[],[f23]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_84,plain,
% 8.06/1.51      ( k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 8.06/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_1089,plain,
% 8.06/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_559,c_84]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_3,plain,
% 8.06/1.51      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 8.06/1.51      inference(cnf_transformation,[],[f25]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_83,plain,
% 8.06/1.51      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 8.06/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_1619,plain,
% 8.06/1.51      ( k2_xboole_0(X0,X0) = X0 ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_1089,c_83]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_3575,plain,
% 8.06/1.51      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_113,c_4,c_601,c_1619]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_3620,plain,
% 8.06/1.51      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_6,c_3575]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_1087,plain,
% 8.06/1.51      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_6,c_84]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_1201,plain,
% 8.06/1.51      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_1087,c_83]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_3713,plain,
% 8.06/1.51      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X0) = k2_xboole_0(X0,X1) ),
% 8.06/1.51      inference(light_normalisation,[status(thm)],[c_3620,c_4,c_1201]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_3943,plain,
% 8.06/1.51      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_3713,c_6]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_1,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.06/1.51      inference(cnf_transformation,[],[f38]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_394,plain,
% 8.06/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_12751,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X1),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X1),X1),k1_xboole_0) ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_3943,c_394]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_8,plain,
% 8.06/1.51      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 8.06/1.51      inference(cnf_transformation,[],[f40]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_106,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_8,c_5]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_9,plain,
% 8.06/1.51      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0 ),
% 8.06/1.51      inference(cnf_transformation,[],[f41]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_89,plain,
% 8.06/1.51      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) = X0 ),
% 8.06/1.51      inference(light_normalisation,[status(thm)],[c_9,c_4]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_594,plain,
% 8.06/1.51      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_559,c_89]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_843,plain,
% 8.06/1.51      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_594,c_4]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_13361,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X0)),k2_xboole_0(X1,X1))) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X1,X1)) ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_12751,c_5,c_106,c_843]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_2103,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_559,c_106]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_2166,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 8.06/1.51      inference(light_normalisation,[status(thm)],[c_2103,c_4,c_559]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_1091,plain,
% 8.06/1.51      ( r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_601,c_84]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_1754,plain,
% 8.06/1.51      ( r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = iProver_top ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_5,c_1091]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_7654,plain,
% 8.06/1.51      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X1,k1_xboole_0)) = iProver_top ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_2166,c_1754]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_7690,plain,
% 8.06/1.51      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_7654,c_843]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_7897,plain,
% 8.06/1.51      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_1,c_7690]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_8271,plain,
% 8.06/1.51      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) = iProver_top ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_1,c_7897]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_530,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_8315,plain,
% 8.06/1.51      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 8.06/1.51      inference(light_normalisation,[status(thm)],[c_8271,c_530]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_8349,plain,
% 8.06/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_8315,c_83]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_397,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k1_xboole_0 ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_8584,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_8349,c_397]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_13362,plain,
% 8.06/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X0)) = k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) ),
% 8.06/1.51      inference(light_normalisation,[status(thm)],[c_13361,c_8584]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_385,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_4,c_5]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_718,plain,
% 8.06/1.51      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) = k1_xboole_0 ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_385,c_559]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_939,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_718,c_1]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_946,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(k1_xboole_0,X0) ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_939,c_4,c_385]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_947,plain,
% 8.06/1.51      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 8.06/1.51      inference(light_normalisation,[status(thm)],[c_946,c_4,c_559]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_13363,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,X1)) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_13362,c_947,c_1619]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_13364,plain,
% 8.06/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_13363,c_1619]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_15831,plain,
% 8.06/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_13364,c_3713]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_1440,plain,
% 8.06/1.51      ( r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = iProver_top ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_397,c_84]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_8583,plain,
% 8.06/1.51      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_8349,c_1440]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_10813,plain,
% 8.06/1.51      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_8583,c_83]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_15171,plain,
% 8.06/1.51      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1)))) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_10813,c_3575]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_15266,plain,
% 8.06/1.51      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1)))),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1)))) = k2_xboole_0(X0,X1) ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_15171,c_10813]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_15268,plain,
% 8.06/1.51      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X1) = k2_xboole_0(X0,X1) ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_15266,c_4,c_530,c_8584]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_7656,plain,
% 8.06/1.51      ( r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X0),k2_xboole_0(X1,k1_xboole_0)) = iProver_top ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_3943,c_1754]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_7684,plain,
% 8.06/1.51      ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X0)),X1) = iProver_top ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_7656,c_5,c_843]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_7685,plain,
% 8.06/1.51      ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = iProver_top ),
% 8.06/1.51      inference(light_normalisation,[status(thm)],[c_7684,c_1619]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_7813,plain,
% 8.06/1.51      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = X1 ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_7685,c_83]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_383,plain,
% 8.06/1.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_8697,plain,
% 8.06/1.51      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_7813,c_383]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_9217,plain,
% 8.06/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 8.06/1.51      inference(light_normalisation,[status(thm)],[c_8697,c_4,c_6]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_15269,plain,
% 8.06/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 8.06/1.51      inference(light_normalisation,[status(thm)],[c_15268,c_9217]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_18325,plain,
% 8.06/1.51      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_15831,c_15269]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_19014,plain,
% 8.06/1.51      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 8.06/1.51      inference(superposition,[status(thm)],[c_18325,c_15831]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_11,negated_conjecture,
% 8.06/1.51      ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) != k2_xboole_0(sK0,sK1) ),
% 8.06/1.51      inference(cnf_transformation,[],[f43]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_109,plain,
% 8.06/1.51      ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))) != k2_xboole_0(sK0,sK1) ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_11,c_106]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_8525,plain,
% 8.06/1.51      ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,sK0)) != k2_xboole_0(sK0,sK1) ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_8349,c_109]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_8526,plain,
% 8.06/1.51      ( k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_8525,c_4,c_559]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_25548,plain,
% 8.06/1.51      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
% 8.06/1.51      inference(demodulation,[status(thm)],[c_19014,c_8526]) ).
% 8.06/1.51  
% 8.06/1.51  cnf(c_25555,plain,
% 8.06/1.51      ( $false ),
% 8.06/1.51      inference(equality_resolution_simp,[status(thm)],[c_25548]) ).
% 8.06/1.51  
% 8.06/1.51  
% 8.06/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 8.06/1.51  
% 8.06/1.51  ------                               Statistics
% 8.06/1.51  
% 8.06/1.51  ------ Selected
% 8.06/1.51  
% 8.06/1.51  total_time:                             0.959
% 8.06/1.51  
%------------------------------------------------------------------------------
