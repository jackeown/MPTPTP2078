%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:02 EST 2020

% Result     : Theorem 12.13s
% Output     : CNFRefutation 12.13s
% Verified   : 
% Statistics : Number of formulae       :  170 (8534 expanded)
%              Number of clauses        :  134 (3464 expanded)
%              Number of leaves         :   14 (2172 expanded)
%              Depth                    :   32
%              Number of atoms          :  178 (9928 expanded)
%              Number of equality atoms :  169 (8335 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f32,f32])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f18,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f33,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f33,f32,f23,f23])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_63,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_7])).

cnf(c_9,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_129,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_63,c_9])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_134,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_129,c_4])).

cnf(c_311,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_134,c_1])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_46,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k4_xboole_0(X3,X1) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_47,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_46])).

cnf(c_107,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_47])).

cnf(c_316,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_311,c_7,c_107])).

cnf(c_587,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_316,c_8])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_10,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_65,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_10])).

cnf(c_50009,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_587,c_65])).

cnf(c_123,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_63,c_9])).

cnf(c_66,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_137,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_123,c_66])).

cnf(c_108,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_63])).

cnf(c_328,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_137,c_108])).

cnf(c_94,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_563,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_47,c_316])).

cnf(c_752,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_563,c_7])).

cnf(c_795,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_752,c_0])).

cnf(c_949,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = X0 ),
    inference(superposition,[status(thm)],[c_94,c_795])).

cnf(c_1038,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X2))) = X0 ),
    inference(demodulation,[status(thm)],[c_949,c_8])).

cnf(c_6115,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_1038])).

cnf(c_18368,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_328,c_6115])).

cnf(c_18593,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_18368,c_7])).

cnf(c_334,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_137,c_1])).

cnf(c_99,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_63,c_8])).

cnf(c_80,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_47,c_7])).

cnf(c_112,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_99,c_80])).

cnf(c_339,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_334,c_7,c_112])).

cnf(c_786,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_339,c_752])).

cnf(c_1483,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_786])).

cnf(c_305,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_134,c_108])).

cnf(c_118,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_8414,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0))),k4_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_305,c_118])).

cnf(c_1658,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1483,c_316])).

cnf(c_1681,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1658,c_107])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_105,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_110,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_105,c_8])).

cnf(c_3614,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_2,c_110])).

cnf(c_3888,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3614,c_108])).

cnf(c_4723,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3888,c_339])).

cnf(c_4739,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_4723,c_7,c_752,c_1681])).

cnf(c_4752,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_4739])).

cnf(c_5027,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X0)))) ),
    inference(superposition,[status(thm)],[c_4752,c_9])).

cnf(c_8568,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)))),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_8414,c_7,c_305,c_1681,c_5027])).

cnf(c_98,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_47,c_8])).

cnf(c_113,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_98,c_8,c_80])).

cnf(c_764,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_752])).

cnf(c_1099,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_113,c_764])).

cnf(c_1138,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_1099,c_8])).

cnf(c_1139,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_1138,c_4])).

cnf(c_868,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_339,c_795])).

cnf(c_4997,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
    inference(superposition,[status(thm)],[c_868,c_4752])).

cnf(c_6563,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X3))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1139,c_4997])).

cnf(c_8569,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_8568,c_6563])).

cnf(c_18594,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_18593,c_1483,c_8569])).

cnf(c_127,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X2,X3)),X1) ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_19056,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X3,X2)),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_18594,c_127])).

cnf(c_165,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_107,c_8])).

cnf(c_100,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_8,c_8])).

cnf(c_111,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_100,c_8])).

cnf(c_170,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_165,c_80,c_111])).

cnf(c_346,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_170])).

cnf(c_84,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_47,c_1])).

cnf(c_87,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_84,c_4,c_8])).

cnf(c_371,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_87])).

cnf(c_85,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_47])).

cnf(c_211,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_85,c_8])).

cnf(c_446,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_137,c_211])).

cnf(c_950,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = X1 ),
    inference(superposition,[status(thm)],[c_94,c_752])).

cnf(c_1037,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = X1 ),
    inference(demodulation,[status(thm)],[c_950,c_8])).

cnf(c_5916,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)),X2) = X2 ),
    inference(superposition,[status(thm)],[c_9,c_1037])).

cnf(c_18063,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_446,c_5916])).

cnf(c_18299,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(light_normalisation,[status(thm)],[c_18063,c_7])).

cnf(c_124,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_11389,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(k4_xboole_0(X1,X2),X2))) ),
    inference(superposition,[status(thm)],[c_446,c_124])).

cnf(c_11721,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(k4_xboole_0(X1,X2),X2))) ),
    inference(light_normalisation,[status(thm)],[c_11389,c_7])).

cnf(c_121,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),X2) ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_10041,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k2_xboole_0(X2,X4))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X3,k2_xboole_0(X2,X4)))),X2) ),
    inference(superposition,[status(thm)],[c_4997,c_121])).

cnf(c_2786,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_1681,c_9])).

cnf(c_2793,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_2786,c_1681])).

cnf(c_2794,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_2793,c_7])).

cnf(c_10685,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_2794,c_1681])).

cnf(c_11722,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_11721,c_446,c_10041,c_10685])).

cnf(c_122,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_47,c_9])).

cnf(c_138,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_122,c_66])).

cnf(c_2868,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_137,c_138])).

cnf(c_11723,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_11722,c_795,c_2868])).

cnf(c_18300,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_18299,c_1483,c_11723])).

cnf(c_18659,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_371,c_18300])).

cnf(c_18888,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(demodulation,[status(thm)],[c_18659,c_764])).

cnf(c_31971,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2),k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_346,c_18888])).

cnf(c_130,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_16928,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_134,c_130])).

cnf(c_17310,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_16928,c_130])).

cnf(c_32228,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_31971,c_17310])).

cnf(c_1644,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_9,c_1483])).

cnf(c_785,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_316,c_752])).

cnf(c_1448,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),X1)) = k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_9,c_785])).

cnf(c_1481,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_1448,c_130])).

cnf(c_1686,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_1644,c_130,c_1481])).

cnf(c_212,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_85,c_9])).

cnf(c_213,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2) = k4_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_212,c_4])).

cnf(c_28215,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_213,c_18300])).

cnf(c_28255,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_213,c_18594])).

cnf(c_18668,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_316,c_18300])).

cnf(c_780,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_134,c_752])).

cnf(c_18878,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_18668,c_780])).

cnf(c_28337,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_28255,c_18878])).

cnf(c_28358,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_28215,c_28337])).

cnf(c_29400,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X2) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_1686,c_28358])).

cnf(c_32229,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_32228,c_7,c_29400])).

cnf(c_274,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_113])).

cnf(c_846,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_795])).

cnf(c_1182,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_274,c_846])).

cnf(c_1204,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1182,c_8])).

cnf(c_1205,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1204,c_4])).

cnf(c_33105,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_32229,c_1205])).

cnf(c_47194,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(k4_xboole_0(X1,X3),X0) ),
    inference(superposition,[status(thm)],[c_127,c_33105])).

cnf(c_50010,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_50009,c_19056,c_47194])).

cnf(c_50011,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_50010,c_47,c_66])).

cnf(c_51376,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1,c_50011])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 12.13/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.13/1.98  
% 12.13/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.13/1.98  
% 12.13/1.98  ------  iProver source info
% 12.13/1.98  
% 12.13/1.98  git: date: 2020-06-30 10:37:57 +0100
% 12.13/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.13/1.98  git: non_committed_changes: false
% 12.13/1.98  git: last_make_outside_of_git: false
% 12.13/1.98  
% 12.13/1.98  ------ 
% 12.13/1.98  
% 12.13/1.98  ------ Input Options
% 12.13/1.98  
% 12.13/1.98  --out_options                           all
% 12.13/1.98  --tptp_safe_out                         true
% 12.13/1.98  --problem_path                          ""
% 12.13/1.98  --include_path                          ""
% 12.13/1.98  --clausifier                            res/vclausify_rel
% 12.13/1.98  --clausifier_options                    --mode clausify
% 12.13/1.98  --stdin                                 false
% 12.13/1.98  --stats_out                             all
% 12.13/1.98  
% 12.13/1.98  ------ General Options
% 12.13/1.98  
% 12.13/1.98  --fof                                   false
% 12.13/1.98  --time_out_real                         305.
% 12.13/1.98  --time_out_virtual                      -1.
% 12.13/1.98  --symbol_type_check                     false
% 12.13/1.98  --clausify_out                          false
% 12.13/1.98  --sig_cnt_out                           false
% 12.13/1.98  --trig_cnt_out                          false
% 12.13/1.98  --trig_cnt_out_tolerance                1.
% 12.13/1.98  --trig_cnt_out_sk_spl                   false
% 12.13/1.98  --abstr_cl_out                          false
% 12.13/1.98  
% 12.13/1.98  ------ Global Options
% 12.13/1.98  
% 12.13/1.98  --schedule                              default
% 12.13/1.98  --add_important_lit                     false
% 12.13/1.98  --prop_solver_per_cl                    1000
% 12.13/1.98  --min_unsat_core                        false
% 12.13/1.98  --soft_assumptions                      false
% 12.13/1.98  --soft_lemma_size                       3
% 12.13/1.98  --prop_impl_unit_size                   0
% 12.13/1.98  --prop_impl_unit                        []
% 12.13/1.98  --share_sel_clauses                     true
% 12.13/1.98  --reset_solvers                         false
% 12.13/1.98  --bc_imp_inh                            [conj_cone]
% 12.13/1.98  --conj_cone_tolerance                   3.
% 12.13/1.98  --extra_neg_conj                        none
% 12.13/1.98  --large_theory_mode                     true
% 12.13/1.98  --prolific_symb_bound                   200
% 12.13/1.98  --lt_threshold                          2000
% 12.13/1.98  --clause_weak_htbl                      true
% 12.13/1.98  --gc_record_bc_elim                     false
% 12.13/1.98  
% 12.13/1.98  ------ Preprocessing Options
% 12.13/1.98  
% 12.13/1.98  --preprocessing_flag                    true
% 12.13/1.98  --time_out_prep_mult                    0.1
% 12.13/1.98  --splitting_mode                        input
% 12.13/1.98  --splitting_grd                         true
% 12.13/1.98  --splitting_cvd                         false
% 12.13/1.98  --splitting_cvd_svl                     false
% 12.13/1.98  --splitting_nvd                         32
% 12.13/1.98  --sub_typing                            true
% 12.13/1.98  --prep_gs_sim                           true
% 12.13/1.98  --prep_unflatten                        true
% 12.13/1.98  --prep_res_sim                          true
% 12.13/1.98  --prep_upred                            true
% 12.13/1.98  --prep_sem_filter                       exhaustive
% 12.13/1.98  --prep_sem_filter_out                   false
% 12.13/1.98  --pred_elim                             true
% 12.13/1.98  --res_sim_input                         true
% 12.13/1.98  --eq_ax_congr_red                       true
% 12.13/1.98  --pure_diseq_elim                       true
% 12.13/1.98  --brand_transform                       false
% 12.13/1.98  --non_eq_to_eq                          false
% 12.13/1.98  --prep_def_merge                        true
% 12.13/1.98  --prep_def_merge_prop_impl              false
% 12.13/1.98  --prep_def_merge_mbd                    true
% 12.13/1.98  --prep_def_merge_tr_red                 false
% 12.13/1.98  --prep_def_merge_tr_cl                  false
% 12.13/1.98  --smt_preprocessing                     true
% 12.13/1.98  --smt_ac_axioms                         fast
% 12.13/1.98  --preprocessed_out                      false
% 12.13/1.98  --preprocessed_stats                    false
% 12.13/1.98  
% 12.13/1.98  ------ Abstraction refinement Options
% 12.13/1.98  
% 12.13/1.98  --abstr_ref                             []
% 12.13/1.98  --abstr_ref_prep                        false
% 12.13/1.98  --abstr_ref_until_sat                   false
% 12.13/1.98  --abstr_ref_sig_restrict                funpre
% 12.13/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 12.13/1.98  --abstr_ref_under                       []
% 12.13/1.98  
% 12.13/1.98  ------ SAT Options
% 12.13/1.98  
% 12.13/1.98  --sat_mode                              false
% 12.13/1.98  --sat_fm_restart_options                ""
% 12.13/1.98  --sat_gr_def                            false
% 12.13/1.98  --sat_epr_types                         true
% 12.13/1.98  --sat_non_cyclic_types                  false
% 12.13/1.98  --sat_finite_models                     false
% 12.13/1.98  --sat_fm_lemmas                         false
% 12.13/1.98  --sat_fm_prep                           false
% 12.13/1.98  --sat_fm_uc_incr                        true
% 12.13/1.98  --sat_out_model                         small
% 12.13/1.98  --sat_out_clauses                       false
% 12.13/1.98  
% 12.13/1.98  ------ QBF Options
% 12.13/1.98  
% 12.13/1.98  --qbf_mode                              false
% 12.13/1.98  --qbf_elim_univ                         false
% 12.13/1.98  --qbf_dom_inst                          none
% 12.13/1.98  --qbf_dom_pre_inst                      false
% 12.13/1.98  --qbf_sk_in                             false
% 12.13/1.98  --qbf_pred_elim                         true
% 12.13/1.98  --qbf_split                             512
% 12.13/1.98  
% 12.13/1.98  ------ BMC1 Options
% 12.13/1.98  
% 12.13/1.98  --bmc1_incremental                      false
% 12.13/1.98  --bmc1_axioms                           reachable_all
% 12.13/1.98  --bmc1_min_bound                        0
% 12.13/1.98  --bmc1_max_bound                        -1
% 12.13/1.98  --bmc1_max_bound_default                -1
% 12.13/1.98  --bmc1_symbol_reachability              true
% 12.13/1.98  --bmc1_property_lemmas                  false
% 12.13/1.98  --bmc1_k_induction                      false
% 12.13/1.98  --bmc1_non_equiv_states                 false
% 12.13/1.98  --bmc1_deadlock                         false
% 12.13/1.98  --bmc1_ucm                              false
% 12.13/1.98  --bmc1_add_unsat_core                   none
% 12.13/1.98  --bmc1_unsat_core_children              false
% 12.13/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 12.13/1.98  --bmc1_out_stat                         full
% 12.13/1.98  --bmc1_ground_init                      false
% 12.13/1.98  --bmc1_pre_inst_next_state              false
% 12.13/1.98  --bmc1_pre_inst_state                   false
% 12.13/1.98  --bmc1_pre_inst_reach_state             false
% 12.13/1.98  --bmc1_out_unsat_core                   false
% 12.13/1.98  --bmc1_aig_witness_out                  false
% 12.13/1.98  --bmc1_verbose                          false
% 12.13/1.98  --bmc1_dump_clauses_tptp                false
% 12.13/1.98  --bmc1_dump_unsat_core_tptp             false
% 12.13/1.98  --bmc1_dump_file                        -
% 12.13/1.98  --bmc1_ucm_expand_uc_limit              128
% 12.13/1.98  --bmc1_ucm_n_expand_iterations          6
% 12.13/1.98  --bmc1_ucm_extend_mode                  1
% 12.13/1.98  --bmc1_ucm_init_mode                    2
% 12.13/1.98  --bmc1_ucm_cone_mode                    none
% 12.13/1.98  --bmc1_ucm_reduced_relation_type        0
% 12.13/1.98  --bmc1_ucm_relax_model                  4
% 12.13/1.98  --bmc1_ucm_full_tr_after_sat            true
% 12.13/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 12.13/1.98  --bmc1_ucm_layered_model                none
% 12.13/1.98  --bmc1_ucm_max_lemma_size               10
% 12.13/1.98  
% 12.13/1.98  ------ AIG Options
% 12.13/1.98  
% 12.13/1.98  --aig_mode                              false
% 12.13/1.98  
% 12.13/1.98  ------ Instantiation Options
% 12.13/1.98  
% 12.13/1.98  --instantiation_flag                    true
% 12.13/1.98  --inst_sos_flag                         false
% 12.13/1.98  --inst_sos_phase                        true
% 12.13/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.13/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.13/1.98  --inst_lit_sel_side                     num_symb
% 12.13/1.98  --inst_solver_per_active                1400
% 12.13/1.98  --inst_solver_calls_frac                1.
% 12.13/1.98  --inst_passive_queue_type               priority_queues
% 12.13/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.13/1.98  --inst_passive_queues_freq              [25;2]
% 12.13/1.98  --inst_dismatching                      true
% 12.13/1.98  --inst_eager_unprocessed_to_passive     true
% 12.13/1.98  --inst_prop_sim_given                   true
% 12.13/1.98  --inst_prop_sim_new                     false
% 12.13/1.98  --inst_subs_new                         false
% 12.13/1.98  --inst_eq_res_simp                      false
% 12.13/1.98  --inst_subs_given                       false
% 12.13/1.98  --inst_orphan_elimination               true
% 12.13/1.98  --inst_learning_loop_flag               true
% 12.13/1.98  --inst_learning_start                   3000
% 12.13/1.98  --inst_learning_factor                  2
% 12.13/1.98  --inst_start_prop_sim_after_learn       3
% 12.13/1.98  --inst_sel_renew                        solver
% 12.13/1.98  --inst_lit_activity_flag                true
% 12.13/1.98  --inst_restr_to_given                   false
% 12.13/1.98  --inst_activity_threshold               500
% 12.13/1.98  --inst_out_proof                        true
% 12.13/1.98  
% 12.13/1.98  ------ Resolution Options
% 12.13/1.98  
% 12.13/1.98  --resolution_flag                       true
% 12.13/1.98  --res_lit_sel                           adaptive
% 12.13/1.98  --res_lit_sel_side                      none
% 12.13/1.98  --res_ordering                          kbo
% 12.13/1.98  --res_to_prop_solver                    active
% 12.13/1.98  --res_prop_simpl_new                    false
% 12.13/1.98  --res_prop_simpl_given                  true
% 12.13/1.98  --res_passive_queue_type                priority_queues
% 12.13/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.13/1.98  --res_passive_queues_freq               [15;5]
% 12.13/1.98  --res_forward_subs                      full
% 12.13/1.98  --res_backward_subs                     full
% 12.13/1.98  --res_forward_subs_resolution           true
% 12.13/1.98  --res_backward_subs_resolution          true
% 12.13/1.98  --res_orphan_elimination                true
% 12.13/1.98  --res_time_limit                        2.
% 12.13/1.98  --res_out_proof                         true
% 12.13/1.98  
% 12.13/1.98  ------ Superposition Options
% 12.13/1.98  
% 12.13/1.98  --superposition_flag                    true
% 12.13/1.98  --sup_passive_queue_type                priority_queues
% 12.13/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.13/1.98  --sup_passive_queues_freq               [8;1;4]
% 12.13/1.98  --demod_completeness_check              fast
% 12.13/1.98  --demod_use_ground                      true
% 12.13/1.98  --sup_to_prop_solver                    passive
% 12.13/1.98  --sup_prop_simpl_new                    true
% 12.13/1.98  --sup_prop_simpl_given                  true
% 12.13/1.98  --sup_fun_splitting                     false
% 12.13/1.98  --sup_smt_interval                      50000
% 12.13/1.98  
% 12.13/1.98  ------ Superposition Simplification Setup
% 12.13/1.98  
% 12.13/1.98  --sup_indices_passive                   []
% 12.13/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.13/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.13/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.13/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 12.13/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.13/1.98  --sup_full_bw                           [BwDemod]
% 12.13/1.98  --sup_immed_triv                        [TrivRules]
% 12.13/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.13/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.13/1.98  --sup_immed_bw_main                     []
% 12.13/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.13/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 12.13/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.13/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.13/1.98  
% 12.13/1.98  ------ Combination Options
% 12.13/1.98  
% 12.13/1.98  --comb_res_mult                         3
% 12.13/1.98  --comb_sup_mult                         2
% 12.13/1.98  --comb_inst_mult                        10
% 12.13/1.98  
% 12.13/1.98  ------ Debug Options
% 12.13/1.98  
% 12.13/1.98  --dbg_backtrace                         false
% 12.13/1.98  --dbg_dump_prop_clauses                 false
% 12.13/1.98  --dbg_dump_prop_clauses_file            -
% 12.13/1.98  --dbg_out_stat                          false
% 12.13/1.98  ------ Parsing...
% 12.13/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.13/1.98  
% 12.13/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 12.13/1.98  
% 12.13/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.13/1.98  
% 12.13/1.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.13/1.98  ------ Proving...
% 12.13/1.98  ------ Problem Properties 
% 12.13/1.98  
% 12.13/1.98  
% 12.13/1.98  clauses                                 10
% 12.13/1.98  conjectures                             1
% 12.13/1.98  EPR                                     0
% 12.13/1.98  Horn                                    10
% 12.13/1.98  unary                                   10
% 12.13/1.98  binary                                  0
% 12.13/1.98  lits                                    10
% 12.13/1.98  lits eq                                 10
% 12.13/1.98  fd_pure                                 0
% 12.13/1.98  fd_pseudo                               0
% 12.13/1.98  fd_cond                                 0
% 12.13/1.98  fd_pseudo_cond                          0
% 12.13/1.98  AC symbols                              0
% 12.13/1.98  
% 12.13/1.98  ------ Schedule UEQ
% 12.13/1.98  
% 12.13/1.98  ------ pure equality problem: resolution off 
% 12.13/1.98  
% 12.13/1.98  ------ Option_UEQ Time Limit: Unbounded
% 12.13/1.98  
% 12.13/1.98  
% 12.13/1.98  ------ 
% 12.13/1.98  Current options:
% 12.13/1.98  ------ 
% 12.13/1.98  
% 12.13/1.98  ------ Input Options
% 12.13/1.98  
% 12.13/1.98  --out_options                           all
% 12.13/1.98  --tptp_safe_out                         true
% 12.13/1.98  --problem_path                          ""
% 12.13/1.98  --include_path                          ""
% 12.13/1.98  --clausifier                            res/vclausify_rel
% 12.13/1.98  --clausifier_options                    --mode clausify
% 12.13/1.98  --stdin                                 false
% 12.13/1.98  --stats_out                             all
% 12.13/1.98  
% 12.13/1.98  ------ General Options
% 12.13/1.98  
% 12.13/1.98  --fof                                   false
% 12.13/1.98  --time_out_real                         305.
% 12.13/1.98  --time_out_virtual                      -1.
% 12.13/1.98  --symbol_type_check                     false
% 12.13/1.98  --clausify_out                          false
% 12.13/1.98  --sig_cnt_out                           false
% 12.13/1.98  --trig_cnt_out                          false
% 12.13/1.98  --trig_cnt_out_tolerance                1.
% 12.13/1.98  --trig_cnt_out_sk_spl                   false
% 12.13/1.98  --abstr_cl_out                          false
% 12.13/1.98  
% 12.13/1.98  ------ Global Options
% 12.13/1.98  
% 12.13/1.98  --schedule                              default
% 12.13/1.98  --add_important_lit                     false
% 12.13/1.98  --prop_solver_per_cl                    1000
% 12.13/1.98  --min_unsat_core                        false
% 12.13/1.98  --soft_assumptions                      false
% 12.13/1.98  --soft_lemma_size                       3
% 12.13/1.98  --prop_impl_unit_size                   0
% 12.13/1.98  --prop_impl_unit                        []
% 12.13/1.98  --share_sel_clauses                     true
% 12.13/1.98  --reset_solvers                         false
% 12.13/1.98  --bc_imp_inh                            [conj_cone]
% 12.13/1.98  --conj_cone_tolerance                   3.
% 12.13/1.98  --extra_neg_conj                        none
% 12.13/1.98  --large_theory_mode                     true
% 12.13/1.98  --prolific_symb_bound                   200
% 12.13/1.98  --lt_threshold                          2000
% 12.13/1.98  --clause_weak_htbl                      true
% 12.13/1.98  --gc_record_bc_elim                     false
% 12.13/1.98  
% 12.13/1.98  ------ Preprocessing Options
% 12.13/1.98  
% 12.13/1.98  --preprocessing_flag                    true
% 12.13/1.98  --time_out_prep_mult                    0.1
% 12.13/1.98  --splitting_mode                        input
% 12.13/1.98  --splitting_grd                         true
% 12.13/1.98  --splitting_cvd                         false
% 12.13/1.98  --splitting_cvd_svl                     false
% 12.13/1.98  --splitting_nvd                         32
% 12.13/1.98  --sub_typing                            true
% 12.13/1.98  --prep_gs_sim                           true
% 12.13/1.98  --prep_unflatten                        true
% 12.13/1.98  --prep_res_sim                          true
% 12.13/1.98  --prep_upred                            true
% 12.13/1.98  --prep_sem_filter                       exhaustive
% 12.13/1.98  --prep_sem_filter_out                   false
% 12.13/1.98  --pred_elim                             true
% 12.13/1.98  --res_sim_input                         true
% 12.13/1.98  --eq_ax_congr_red                       true
% 12.13/1.98  --pure_diseq_elim                       true
% 12.13/1.98  --brand_transform                       false
% 12.13/1.98  --non_eq_to_eq                          false
% 12.13/1.98  --prep_def_merge                        true
% 12.13/1.98  --prep_def_merge_prop_impl              false
% 12.13/1.98  --prep_def_merge_mbd                    true
% 12.13/1.98  --prep_def_merge_tr_red                 false
% 12.13/1.98  --prep_def_merge_tr_cl                  false
% 12.13/1.98  --smt_preprocessing                     true
% 12.13/1.98  --smt_ac_axioms                         fast
% 12.13/1.98  --preprocessed_out                      false
% 12.13/1.98  --preprocessed_stats                    false
% 12.13/1.98  
% 12.13/1.98  ------ Abstraction refinement Options
% 12.13/1.98  
% 12.13/1.98  --abstr_ref                             []
% 12.13/1.98  --abstr_ref_prep                        false
% 12.13/1.98  --abstr_ref_until_sat                   false
% 12.13/1.98  --abstr_ref_sig_restrict                funpre
% 12.13/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 12.13/1.98  --abstr_ref_under                       []
% 12.13/1.98  
% 12.13/1.98  ------ SAT Options
% 12.13/1.98  
% 12.13/1.98  --sat_mode                              false
% 12.13/1.98  --sat_fm_restart_options                ""
% 12.13/1.98  --sat_gr_def                            false
% 12.13/1.98  --sat_epr_types                         true
% 12.13/1.98  --sat_non_cyclic_types                  false
% 12.13/1.98  --sat_finite_models                     false
% 12.13/1.98  --sat_fm_lemmas                         false
% 12.13/1.98  --sat_fm_prep                           false
% 12.13/1.98  --sat_fm_uc_incr                        true
% 12.13/1.98  --sat_out_model                         small
% 12.13/1.98  --sat_out_clauses                       false
% 12.13/1.98  
% 12.13/1.98  ------ QBF Options
% 12.13/1.98  
% 12.13/1.98  --qbf_mode                              false
% 12.13/1.98  --qbf_elim_univ                         false
% 12.13/1.98  --qbf_dom_inst                          none
% 12.13/1.98  --qbf_dom_pre_inst                      false
% 12.13/1.98  --qbf_sk_in                             false
% 12.13/1.98  --qbf_pred_elim                         true
% 12.13/1.98  --qbf_split                             512
% 12.13/1.98  
% 12.13/1.98  ------ BMC1 Options
% 12.13/1.98  
% 12.13/1.98  --bmc1_incremental                      false
% 12.13/1.98  --bmc1_axioms                           reachable_all
% 12.13/1.98  --bmc1_min_bound                        0
% 12.13/1.98  --bmc1_max_bound                        -1
% 12.13/1.98  --bmc1_max_bound_default                -1
% 12.13/1.98  --bmc1_symbol_reachability              true
% 12.13/1.98  --bmc1_property_lemmas                  false
% 12.13/1.98  --bmc1_k_induction                      false
% 12.13/1.98  --bmc1_non_equiv_states                 false
% 12.13/1.98  --bmc1_deadlock                         false
% 12.13/1.98  --bmc1_ucm                              false
% 12.13/1.98  --bmc1_add_unsat_core                   none
% 12.13/1.98  --bmc1_unsat_core_children              false
% 12.13/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 12.13/1.98  --bmc1_out_stat                         full
% 12.13/1.98  --bmc1_ground_init                      false
% 12.13/1.98  --bmc1_pre_inst_next_state              false
% 12.13/1.98  --bmc1_pre_inst_state                   false
% 12.13/1.98  --bmc1_pre_inst_reach_state             false
% 12.13/1.98  --bmc1_out_unsat_core                   false
% 12.13/1.98  --bmc1_aig_witness_out                  false
% 12.13/1.98  --bmc1_verbose                          false
% 12.13/1.98  --bmc1_dump_clauses_tptp                false
% 12.13/1.98  --bmc1_dump_unsat_core_tptp             false
% 12.13/1.98  --bmc1_dump_file                        -
% 12.13/1.98  --bmc1_ucm_expand_uc_limit              128
% 12.13/1.98  --bmc1_ucm_n_expand_iterations          6
% 12.13/1.98  --bmc1_ucm_extend_mode                  1
% 12.13/1.98  --bmc1_ucm_init_mode                    2
% 12.13/1.98  --bmc1_ucm_cone_mode                    none
% 12.13/1.98  --bmc1_ucm_reduced_relation_type        0
% 12.13/1.98  --bmc1_ucm_relax_model                  4
% 12.13/1.98  --bmc1_ucm_full_tr_after_sat            true
% 12.13/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 12.13/1.98  --bmc1_ucm_layered_model                none
% 12.13/1.98  --bmc1_ucm_max_lemma_size               10
% 12.13/1.98  
% 12.13/1.98  ------ AIG Options
% 12.13/1.98  
% 12.13/1.98  --aig_mode                              false
% 12.13/1.98  
% 12.13/1.98  ------ Instantiation Options
% 12.13/1.98  
% 12.13/1.98  --instantiation_flag                    false
% 12.13/1.98  --inst_sos_flag                         false
% 12.13/1.98  --inst_sos_phase                        true
% 12.13/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.13/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.13/1.98  --inst_lit_sel_side                     num_symb
% 12.13/1.98  --inst_solver_per_active                1400
% 12.13/1.98  --inst_solver_calls_frac                1.
% 12.13/1.98  --inst_passive_queue_type               priority_queues
% 12.13/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.13/1.98  --inst_passive_queues_freq              [25;2]
% 12.13/1.98  --inst_dismatching                      true
% 12.13/1.98  --inst_eager_unprocessed_to_passive     true
% 12.13/1.98  --inst_prop_sim_given                   true
% 12.13/1.98  --inst_prop_sim_new                     false
% 12.13/1.98  --inst_subs_new                         false
% 12.13/1.98  --inst_eq_res_simp                      false
% 12.13/1.98  --inst_subs_given                       false
% 12.13/1.98  --inst_orphan_elimination               true
% 12.13/1.98  --inst_learning_loop_flag               true
% 12.13/1.98  --inst_learning_start                   3000
% 12.13/1.98  --inst_learning_factor                  2
% 12.13/1.98  --inst_start_prop_sim_after_learn       3
% 12.13/1.98  --inst_sel_renew                        solver
% 12.13/1.98  --inst_lit_activity_flag                true
% 12.13/1.98  --inst_restr_to_given                   false
% 12.13/1.98  --inst_activity_threshold               500
% 12.13/1.98  --inst_out_proof                        true
% 12.13/1.98  
% 12.13/1.98  ------ Resolution Options
% 12.13/1.98  
% 12.13/1.98  --resolution_flag                       false
% 12.13/1.98  --res_lit_sel                           adaptive
% 12.13/1.98  --res_lit_sel_side                      none
% 12.13/1.98  --res_ordering                          kbo
% 12.13/1.98  --res_to_prop_solver                    active
% 12.13/1.98  --res_prop_simpl_new                    false
% 12.13/1.98  --res_prop_simpl_given                  true
% 12.13/1.98  --res_passive_queue_type                priority_queues
% 12.13/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.13/1.98  --res_passive_queues_freq               [15;5]
% 12.13/1.98  --res_forward_subs                      full
% 12.13/1.98  --res_backward_subs                     full
% 12.13/1.98  --res_forward_subs_resolution           true
% 12.13/1.98  --res_backward_subs_resolution          true
% 12.13/1.98  --res_orphan_elimination                true
% 12.13/1.98  --res_time_limit                        2.
% 12.13/1.98  --res_out_proof                         true
% 12.13/1.98  
% 12.13/1.98  ------ Superposition Options
% 12.13/1.98  
% 12.13/1.98  --superposition_flag                    true
% 12.13/1.98  --sup_passive_queue_type                priority_queues
% 12.13/1.98  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.13/1.98  --sup_passive_queues_freq               [8;1;4]
% 12.13/1.98  --demod_completeness_check              fast
% 12.13/1.98  --demod_use_ground                      true
% 12.13/1.98  --sup_to_prop_solver                    active
% 12.13/1.98  --sup_prop_simpl_new                    false
% 12.13/1.98  --sup_prop_simpl_given                  false
% 12.13/1.98  --sup_fun_splitting                     true
% 12.13/1.98  --sup_smt_interval                      10000
% 12.13/1.98  
% 12.13/1.98  ------ Superposition Simplification Setup
% 12.13/1.98  
% 12.13/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.13/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.13/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.13/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.13/1.98  --sup_full_triv                         [TrivRules]
% 12.13/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.13/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.13/1.98  --sup_immed_triv                        [TrivRules]
% 12.13/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.13/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.13/1.98  --sup_immed_bw_main                     []
% 12.13/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.13/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 12.13/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.13/1.98  --sup_input_bw                          [BwDemod;BwSubsumption]
% 12.13/1.98  
% 12.13/1.98  ------ Combination Options
% 12.13/1.98  
% 12.13/1.98  --comb_res_mult                         1
% 12.13/1.98  --comb_sup_mult                         1
% 12.13/1.98  --comb_inst_mult                        1000000
% 12.13/1.98  
% 12.13/1.98  ------ Debug Options
% 12.13/1.98  
% 12.13/1.98  --dbg_backtrace                         false
% 12.13/1.98  --dbg_dump_prop_clauses                 false
% 12.13/1.98  --dbg_dump_prop_clauses_file            -
% 12.13/1.98  --dbg_out_stat                          false
% 12.13/1.98  
% 12.13/1.98  
% 12.13/1.98  
% 12.13/1.98  
% 12.13/1.98  ------ Proving...
% 12.13/1.98  
% 12.13/1.98  
% 12.13/1.98  % SZS status Theorem for theBenchmark.p
% 12.13/1.98  
% 12.13/1.98   Resolution empty clause
% 12.13/1.98  
% 12.13/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 12.13/1.98  
% 12.13/1.98  fof(f2,axiom,(
% 12.13/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 12.13/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.98  
% 12.13/1.98  fof(f22,plain,(
% 12.13/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 12.13/1.98    inference(cnf_transformation,[],[f2])).
% 12.13/1.98  
% 12.13/1.98  fof(f12,axiom,(
% 12.13/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 12.13/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.98  
% 12.13/1.98  fof(f32,plain,(
% 12.13/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 12.13/1.98    inference(cnf_transformation,[],[f12])).
% 12.13/1.98  
% 12.13/1.98  fof(f34,plain,(
% 12.13/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 12.13/1.98    inference(definition_unfolding,[],[f22,f32,f32])).
% 12.13/1.98  
% 12.13/1.98  fof(f7,axiom,(
% 12.13/1.98    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 12.13/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.98  
% 12.13/1.98  fof(f27,plain,(
% 12.13/1.98    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 12.13/1.98    inference(cnf_transformation,[],[f7])).
% 12.13/1.98  
% 12.13/1.98  fof(f35,plain,(
% 12.13/1.98    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 12.13/1.98    inference(definition_unfolding,[],[f27,f32])).
% 12.13/1.98  
% 12.13/1.98  fof(f9,axiom,(
% 12.13/1.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 12.13/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.98  
% 12.13/1.98  fof(f29,plain,(
% 12.13/1.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.13/1.98    inference(cnf_transformation,[],[f9])).
% 12.13/1.98  
% 12.13/1.98  fof(f11,axiom,(
% 12.13/1.98    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 12.13/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.98  
% 12.13/1.98  fof(f31,plain,(
% 12.13/1.98    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 12.13/1.98    inference(cnf_transformation,[],[f11])).
% 12.13/1.98  
% 12.13/1.98  fof(f6,axiom,(
% 12.13/1.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 12.13/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.98  
% 12.13/1.98  fof(f26,plain,(
% 12.13/1.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.13/1.98    inference(cnf_transformation,[],[f6])).
% 12.13/1.98  
% 12.13/1.98  fof(f10,axiom,(
% 12.13/1.98    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 12.13/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.98  
% 12.13/1.98  fof(f30,plain,(
% 12.13/1.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 12.13/1.98    inference(cnf_transformation,[],[f10])).
% 12.13/1.98  
% 12.13/1.98  fof(f5,axiom,(
% 12.13/1.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 12.13/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.98  
% 12.13/1.98  fof(f16,plain,(
% 12.13/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 12.13/1.98    inference(unused_predicate_definition_removal,[],[f5])).
% 12.13/1.98  
% 12.13/1.98  fof(f17,plain,(
% 12.13/1.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 12.13/1.98    inference(ennf_transformation,[],[f16])).
% 12.13/1.98  
% 12.13/1.98  fof(f25,plain,(
% 12.13/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 12.13/1.98    inference(cnf_transformation,[],[f17])).
% 12.13/1.98  
% 12.13/1.98  fof(f8,axiom,(
% 12.13/1.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 12.13/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.98  
% 12.13/1.98  fof(f28,plain,(
% 12.13/1.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 12.13/1.98    inference(cnf_transformation,[],[f8])).
% 12.13/1.98  
% 12.13/1.98  fof(f1,axiom,(
% 12.13/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 12.13/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.98  
% 12.13/1.98  fof(f21,plain,(
% 12.13/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 12.13/1.98    inference(cnf_transformation,[],[f1])).
% 12.13/1.98  
% 12.13/1.98  fof(f13,conjecture,(
% 12.13/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 12.13/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.98  
% 12.13/1.98  fof(f14,negated_conjecture,(
% 12.13/1.98    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 12.13/1.98    inference(negated_conjecture,[],[f13])).
% 12.13/1.98  
% 12.13/1.98  fof(f18,plain,(
% 12.13/1.98    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 12.13/1.98    inference(ennf_transformation,[],[f14])).
% 12.13/1.98  
% 12.13/1.98  fof(f19,plain,(
% 12.13/1.98    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 12.13/1.98    introduced(choice_axiom,[])).
% 12.13/1.98  
% 12.13/1.98  fof(f20,plain,(
% 12.13/1.98    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 12.13/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 12.13/1.98  
% 12.13/1.98  fof(f33,plain,(
% 12.13/1.98    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 12.13/1.98    inference(cnf_transformation,[],[f20])).
% 12.13/1.98  
% 12.13/1.98  fof(f3,axiom,(
% 12.13/1.98    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 12.13/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.98  
% 12.13/1.98  fof(f23,plain,(
% 12.13/1.98    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 12.13/1.98    inference(cnf_transformation,[],[f3])).
% 12.13/1.98  
% 12.13/1.98  fof(f36,plain,(
% 12.13/1.98    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 12.13/1.98    inference(definition_unfolding,[],[f33,f32,f23,f23])).
% 12.13/1.98  
% 12.13/1.98  fof(f4,axiom,(
% 12.13/1.98    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 12.13/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.98  
% 12.13/1.98  fof(f15,plain,(
% 12.13/1.98    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 12.13/1.98    inference(rectify,[],[f4])).
% 12.13/1.98  
% 12.13/1.98  fof(f24,plain,(
% 12.13/1.98    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 12.13/1.98    inference(cnf_transformation,[],[f15])).
% 12.13/1.98  
% 12.13/1.98  cnf(c_1,plain,
% 12.13/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 12.13/1.98      inference(cnf_transformation,[],[f34]) ).
% 12.13/1.98  
% 12.13/1.98  cnf(c_5,plain,
% 12.13/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 12.13/1.98      inference(cnf_transformation,[],[f35]) ).
% 12.13/1.98  
% 12.13/1.98  cnf(c_7,plain,
% 12.13/1.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 12.13/1.98      inference(cnf_transformation,[],[f29]) ).
% 12.13/1.98  
% 12.13/1.98  cnf(c_63,plain,
% 12.13/1.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 12.13/1.98      inference(light_normalisation,[status(thm)],[c_5,c_7]) ).
% 12.13/1.98  
% 12.13/1.98  cnf(c_9,plain,
% 12.13/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 12.13/1.98      inference(cnf_transformation,[],[f31]) ).
% 12.13/1.98  
% 12.13/1.98  cnf(c_129,plain,
% 12.13/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 12.13/1.98      inference(superposition,[status(thm)],[c_63,c_9]) ).
% 12.13/1.98  
% 12.13/1.98  cnf(c_4,plain,
% 12.13/1.98      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 12.13/1.98      inference(cnf_transformation,[],[f26]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_134,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_129,c_4]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_311,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_134,c_1]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_8,plain,
% 12.13/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 12.13/1.99      inference(cnf_transformation,[],[f30]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_3,plain,
% 12.13/1.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 12.13/1.99      inference(cnf_transformation,[],[f25]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_6,plain,
% 12.13/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 12.13/1.99      inference(cnf_transformation,[],[f28]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_46,plain,
% 12.13/1.99      ( X0 != X1
% 12.13/1.99      | k4_xboole_0(X0,X2) != X3
% 12.13/1.99      | k4_xboole_0(X3,X1) = k1_xboole_0 ),
% 12.13/1.99      inference(resolution_lifted,[status(thm)],[c_3,c_6]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_47,plain,
% 12.13/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 12.13/1.99      inference(unflattening,[status(thm)],[c_46]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_107,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_8,c_47]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_316,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 12.13/1.99      inference(light_normalisation,[status(thm)],[c_311,c_7,c_107]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_587,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_316,c_8]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_0,plain,
% 12.13/1.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 12.13/1.99      inference(cnf_transformation,[],[f21]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_10,negated_conjecture,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 12.13/1.99      inference(cnf_transformation,[],[f36]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_65,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_0,c_10]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_50009,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_587,c_65]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_123,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_63,c_9]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_66,plain,
% 12.13/1.99      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_137,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_123,c_66]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_108,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_8,c_63]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_328,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_137,c_108]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_94,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_563,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) = X0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_47,c_316]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_752,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_563,c_7]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_795,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_752,c_0]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_949,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = X0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_94,c_795]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1038,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X2))) = X0 ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_949,c_8]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_6115,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X0))) = X0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_9,c_1038]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_18368,plain,
% 12.13/1.99      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_328,c_6115]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_18593,plain,
% 12.13/1.99      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 12.13/1.99      inference(light_normalisation,[status(thm)],[c_18368,c_7]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_334,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_137,c_1]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_99,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_63,c_8]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_80,plain,
% 12.13/1.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_47,c_7]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_112,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_99,c_80]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_339,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 12.13/1.99      inference(light_normalisation,[status(thm)],[c_334,c_7,c_112]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_786,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_339,c_752]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1483,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_0,c_786]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_305,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_134,c_108]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_118,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X0)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_8414,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0))),k4_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_305,c_118]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1658,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_1483,c_316]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1681,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 12.13/1.99      inference(light_normalisation,[status(thm)],[c_1658,c_107]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_2,plain,
% 12.13/1.99      ( k2_xboole_0(X0,X0) = X0 ),
% 12.13/1.99      inference(cnf_transformation,[],[f24]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_105,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_110,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_105,c_8]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_3614,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_2,c_110]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_3888,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_3614,c_108]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_4723,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_3888,c_339]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_4739,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_4723,c_7,c_752,c_1681]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_4752,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_8,c_4739]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_5027,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X0)))) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_4752,c_9]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_8568,plain,
% 12.13/1.99      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)))),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_8414,c_7,c_305,c_1681,c_5027]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_98,plain,
% 12.13/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_47,c_8]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_113,plain,
% 12.13/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_98,c_8,c_80]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_764,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_1,c_752]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1099,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_113,c_764]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1138,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_1099,c_8]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1139,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_1138,c_4]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_868,plain,
% 12.13/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_339,c_795]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_4997,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_868,c_4752]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_6563,plain,
% 12.13/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X3))) = k4_xboole_0(X0,X1) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_1139,c_4997]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_8569,plain,
% 12.13/1.99      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_8568,c_6563]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_18594,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_18593,c_1483,c_8569]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_127,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X2,X3)),X1) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_19056,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X3,X2)),k4_xboole_0(X1,X2)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_18594,c_127]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_165,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_107,c_8]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_100,plain,
% 12.13/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_8,c_8]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_111,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_100,c_8]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_170,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_165,c_80,c_111]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_346,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_0,c_170]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_84,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_47,c_1]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_87,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_84,c_4,c_8]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_371,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_1,c_87]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_85,plain,
% 12.13/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_1,c_47]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_211,plain,
% 12.13/1.99      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_85,c_8]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_446,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k1_xboole_0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_137,c_211]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_950,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = X1 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_94,c_752]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1037,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = X1 ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_950,c_8]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_5916,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)),X2) = X2 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_9,c_1037]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_18063,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_446,c_5916]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_18299,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 12.13/1.99      inference(light_normalisation,[status(thm)],[c_18063,c_7]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_124,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_11389,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(k4_xboole_0(X1,X2),X2))) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_446,c_124]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_11721,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(k4_xboole_0(X1,X2),X2))) ),
% 12.13/1.99      inference(light_normalisation,[status(thm)],[c_11389,c_7]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_121,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),X2) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_10041,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k2_xboole_0(X2,X4))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X3,k2_xboole_0(X2,X4)))),X2) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_4997,c_121]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_2786,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X2,X1)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_1681,c_9]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_2793,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_2786,c_1681]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_2794,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 12.13/1.99      inference(light_normalisation,[status(thm)],[c_2793,c_7]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_10685,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_2794,c_1681]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_11722,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_11721,c_446,c_10041,c_10685]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_122,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X0)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_47,c_9]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_138,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,X0) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_122,c_66]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_2868,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_137,c_138]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_11723,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_11722,c_795,c_2868]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_18300,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_18299,c_1483,c_11723]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_18659,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_371,c_18300]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_18888,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_18659,c_764]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_31971,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2),k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_346,c_18888]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_130,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_16928,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_134,c_130]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_17310,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_16928,c_130]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_32228,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 12.13/1.99      inference(light_normalisation,[status(thm)],[c_31971,c_17310]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1644,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_9,c_1483]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_785,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_316,c_752]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1448,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),X1)) = k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_9,c_785]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1481,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_1448,c_130]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1686,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 12.13/1.99      inference(light_normalisation,[status(thm)],[c_1644,c_130,c_1481]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_212,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k1_xboole_0) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_85,c_9]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_213,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2) = k4_xboole_0(X0,X2) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_212,c_4]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_28215,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_213,c_18300]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_28255,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_213,c_18594]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_18668,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_316,c_18300]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_780,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_134,c_752]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_18878,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 12.13/1.99      inference(light_normalisation,[status(thm)],[c_18668,c_780]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_28337,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k2_xboole_0(X1,X0) ),
% 12.13/1.99      inference(light_normalisation,[status(thm)],[c_28255,c_18878]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_28358,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_28215,c_28337]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_29400,plain,
% 12.13/1.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X2) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_1686,c_28358]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_32229,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_32228,c_7,c_29400]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_274,plain,
% 12.13/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_0,c_113]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_846,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_1,c_795]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1182,plain,
% 12.13/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0)) = k2_xboole_0(X0,X1) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_274,c_846]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1204,plain,
% 12.13/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))) = k2_xboole_0(X0,X1) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_1182,c_8]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1205,plain,
% 12.13/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(X0,X1) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_1204,c_4]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_33105,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_32229,c_1205]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_47194,plain,
% 12.13/1.99      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(k4_xboole_0(X1,X3),X0) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_127,c_33105]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_50010,plain,
% 12.13/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_50009,c_19056,c_47194]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_50011,plain,
% 12.13/1.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_50010,c_47,c_66]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_51376,plain,
% 12.13/1.99      ( $false ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_1,c_50011]) ).
% 12.13/1.99  
% 12.13/1.99  
% 12.13/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 12.13/1.99  
% 12.13/1.99  ------                               Statistics
% 12.13/1.99  
% 12.13/1.99  ------ General
% 12.13/1.99  
% 12.13/1.99  abstr_ref_over_cycles:                  0
% 12.13/1.99  abstr_ref_under_cycles:                 0
% 12.13/1.99  gc_basic_clause_elim:                   0
% 12.13/1.99  forced_gc_time:                         0
% 12.13/1.99  parsing_time:                           0.012
% 12.13/1.99  unif_index_cands_time:                  0.
% 12.13/1.99  unif_index_add_time:                    0.
% 12.13/1.99  orderings_time:                         0.
% 12.13/1.99  out_proof_time:                         0.009
% 12.13/1.99  total_time:                             1.479
% 12.13/1.99  num_of_symbols:                         39
% 12.13/1.99  num_of_terms:                           82383
% 12.13/1.99  
% 12.13/1.99  ------ Preprocessing
% 12.13/1.99  
% 12.13/1.99  num_of_splits:                          0
% 12.13/1.99  num_of_split_atoms:                     2
% 12.13/1.99  num_of_reused_defs:                     5
% 12.13/1.99  num_eq_ax_congr_red:                    1
% 12.13/1.99  num_of_sem_filtered_clauses:            0
% 12.13/1.99  num_of_subtypes:                        0
% 12.13/1.99  monotx_restored_types:                  0
% 12.13/1.99  sat_num_of_epr_types:                   0
% 12.13/1.99  sat_num_of_non_cyclic_types:            0
% 12.13/1.99  sat_guarded_non_collapsed_types:        0
% 12.13/1.99  num_pure_diseq_elim:                    0
% 12.13/1.99  simp_replaced_by:                       0
% 12.13/1.99  res_preprocessed:                       35
% 12.13/1.99  prep_upred:                             0
% 12.13/1.99  prep_unflattend:                        2
% 12.13/1.99  smt_new_axioms:                         0
% 12.13/1.99  pred_elim_cands:                        0
% 12.13/1.99  pred_elim:                              1
% 12.13/1.99  pred_elim_cl:                           1
% 12.13/1.99  pred_elim_cycles:                       2
% 12.13/1.99  merged_defs:                            0
% 12.13/1.99  merged_defs_ncl:                        0
% 12.13/1.99  bin_hyper_res:                          0
% 12.13/1.99  prep_cycles:                            3
% 12.13/1.99  pred_elim_time:                         0.
% 12.13/1.99  splitting_time:                         0.
% 12.13/1.99  sem_filter_time:                        0.
% 12.13/1.99  monotx_time:                            0.
% 12.13/1.99  subtype_inf_time:                       0.
% 12.13/1.99  
% 12.13/1.99  ------ Problem properties
% 12.13/1.99  
% 12.13/1.99  clauses:                                10
% 12.13/1.99  conjectures:                            1
% 12.13/1.99  epr:                                    0
% 12.13/1.99  horn:                                   10
% 12.13/1.99  ground:                                 1
% 12.13/1.99  unary:                                  10
% 12.13/1.99  binary:                                 0
% 12.13/1.99  lits:                                   10
% 12.13/1.99  lits_eq:                                10
% 12.13/1.99  fd_pure:                                0
% 12.13/1.99  fd_pseudo:                              0
% 12.13/1.99  fd_cond:                                0
% 12.13/1.99  fd_pseudo_cond:                         0
% 12.13/1.99  ac_symbols:                             1
% 12.13/1.99  
% 12.13/1.99  ------ Propositional Solver
% 12.13/1.99  
% 12.13/1.99  prop_solver_calls:                      17
% 12.13/1.99  prop_fast_solver_calls:                 85
% 12.13/1.99  smt_solver_calls:                       0
% 12.13/1.99  smt_fast_solver_calls:                  0
% 12.13/1.99  prop_num_of_clauses:                    342
% 12.13/1.99  prop_preprocess_simplified:             566
% 12.13/1.99  prop_fo_subsumed:                       0
% 12.13/1.99  prop_solver_time:                       0.
% 12.13/1.99  smt_solver_time:                        0.
% 12.13/1.99  smt_fast_solver_time:                   0.
% 12.13/1.99  prop_fast_solver_time:                  0.
% 12.13/1.99  prop_unsat_core_time:                   0.
% 12.13/1.99  
% 12.13/1.99  ------ QBF
% 12.13/1.99  
% 12.13/1.99  qbf_q_res:                              0
% 12.13/1.99  qbf_num_tautologies:                    0
% 12.13/1.99  qbf_prep_cycles:                        0
% 12.13/1.99  
% 12.13/1.99  ------ BMC1
% 12.13/1.99  
% 12.13/1.99  bmc1_current_bound:                     -1
% 12.13/1.99  bmc1_last_solved_bound:                 -1
% 12.13/1.99  bmc1_unsat_core_size:                   -1
% 12.13/1.99  bmc1_unsat_core_parents_size:           -1
% 12.13/1.99  bmc1_merge_next_fun:                    0
% 12.13/1.99  bmc1_unsat_core_clauses_time:           0.
% 12.13/1.99  
% 12.13/1.99  ------ Instantiation
% 12.13/1.99  
% 12.13/1.99  inst_num_of_clauses:                    0
% 12.13/1.99  inst_num_in_passive:                    0
% 12.13/1.99  inst_num_in_active:                     0
% 12.13/1.99  inst_num_in_unprocessed:                0
% 12.13/1.99  inst_num_of_loops:                      0
% 12.13/1.99  inst_num_of_learning_restarts:          0
% 12.13/1.99  inst_num_moves_active_passive:          0
% 12.13/1.99  inst_lit_activity:                      0
% 12.13/1.99  inst_lit_activity_moves:                0
% 12.13/1.99  inst_num_tautologies:                   0
% 12.13/1.99  inst_num_prop_implied:                  0
% 12.13/1.99  inst_num_existing_simplified:           0
% 12.13/1.99  inst_num_eq_res_simplified:             0
% 12.13/1.99  inst_num_child_elim:                    0
% 12.13/1.99  inst_num_of_dismatching_blockings:      0
% 12.13/1.99  inst_num_of_non_proper_insts:           0
% 12.13/1.99  inst_num_of_duplicates:                 0
% 12.13/1.99  inst_inst_num_from_inst_to_res:         0
% 12.13/1.99  inst_dismatching_checking_time:         0.
% 12.13/1.99  
% 12.13/1.99  ------ Resolution
% 12.13/1.99  
% 12.13/1.99  res_num_of_clauses:                     0
% 12.13/1.99  res_num_in_passive:                     0
% 12.13/1.99  res_num_in_active:                      0
% 12.13/1.99  res_num_of_loops:                       38
% 12.13/1.99  res_forward_subset_subsumed:            0
% 12.13/1.99  res_backward_subset_subsumed:           0
% 12.13/1.99  res_forward_subsumed:                   0
% 12.13/1.99  res_backward_subsumed:                  0
% 12.13/1.99  res_forward_subsumption_resolution:     0
% 12.13/1.99  res_backward_subsumption_resolution:    0
% 12.13/1.99  res_clause_to_clause_subsumption:       138610
% 12.13/1.99  res_orphan_elimination:                 0
% 12.13/1.99  res_tautology_del:                      0
% 12.13/1.99  res_num_eq_res_simplified:              0
% 12.13/1.99  res_num_sel_changes:                    0
% 12.13/1.99  res_moves_from_active_to_pass:          0
% 12.13/1.99  
% 12.13/1.99  ------ Superposition
% 12.13/1.99  
% 12.13/1.99  sup_time_total:                         0.
% 12.13/1.99  sup_time_generating:                    0.
% 12.13/1.99  sup_time_sim_full:                      0.
% 12.13/1.99  sup_time_sim_immed:                     0.
% 12.13/1.99  
% 12.13/1.99  sup_num_of_clauses:                     5656
% 12.13/1.99  sup_num_in_active:                      159
% 12.13/1.99  sup_num_in_passive:                     5497
% 12.13/1.99  sup_num_of_loops:                       198
% 12.13/1.99  sup_fw_superposition:                   19304
% 12.13/1.99  sup_bw_superposition:                   16062
% 12.13/1.99  sup_immediate_simplified:               15064
% 12.13/1.99  sup_given_eliminated:                   9
% 12.13/1.99  comparisons_done:                       0
% 12.13/1.99  comparisons_avoided:                    0
% 12.13/1.99  
% 12.13/1.99  ------ Simplifications
% 12.13/1.99  
% 12.13/1.99  
% 12.13/1.99  sim_fw_subset_subsumed:                 0
% 12.13/1.99  sim_bw_subset_subsumed:                 0
% 12.13/1.99  sim_fw_subsumed:                        2265
% 12.13/1.99  sim_bw_subsumed:                        83
% 12.13/1.99  sim_fw_subsumption_res:                 0
% 12.13/1.99  sim_bw_subsumption_res:                 0
% 12.13/1.99  sim_tautology_del:                      0
% 12.13/1.99  sim_eq_tautology_del:                   4496
% 12.13/1.99  sim_eq_res_simp:                        0
% 12.13/1.99  sim_fw_demodulated:                     10150
% 12.13/1.99  sim_bw_demodulated:                     200
% 12.13/1.99  sim_light_normalised:                   5373
% 12.13/1.99  sim_joinable_taut:                      82
% 12.13/1.99  sim_joinable_simp:                      0
% 12.13/1.99  sim_ac_normalised:                      0
% 12.13/1.99  sim_smt_subsumption:                    0
% 12.13/1.99  
%------------------------------------------------------------------------------
