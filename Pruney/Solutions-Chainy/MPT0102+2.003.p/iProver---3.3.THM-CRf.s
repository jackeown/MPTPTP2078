%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:02 EST 2020

% Result     : Theorem 11.71s
% Output     : CNFRefutation 11.71s
% Verified   : 
% Statistics : Number of formulae       :  159 (18046 expanded)
%              Number of clauses        :  124 (7560 expanded)
%              Number of leaves         :   14 (4359 expanded)
%              Depth                    :   30
%              Number of atoms          :  167 (22905 expanded)
%              Number of equality atoms :  158 (17352 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f32,f32])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f33,f32,f23,f23])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_7,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_92,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_46,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k4_xboole_0(X3,X1) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_5])).

cnf(c_47,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_46])).

cnf(c_117,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_47])).

cnf(c_381,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_92,c_6,c_117])).

cnf(c_409,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_381,c_8])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_10,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_63,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_10])).

cnf(c_48270,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_409,c_63])).

cnf(c_81,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_213,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_81,c_1])).

cnf(c_74,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_47])).

cnf(c_109,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_74,c_8])).

cnf(c_77,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_47,c_6])).

cnf(c_122,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_109,c_77])).

cnf(c_218,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_213,c_6,c_122])).

cnf(c_118,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_74])).

cnf(c_443,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_218,c_118])).

cnf(c_103,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_394,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_47,c_381])).

cnf(c_701,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_394,c_6])).

cnf(c_742,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_701,c_0])).

cnf(c_1488,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = X0 ),
    inference(superposition,[status(thm)],[c_103,c_742])).

cnf(c_1584,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X2))) = X0 ),
    inference(demodulation,[status(thm)],[c_1488,c_8])).

cnf(c_10981,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(k1_xboole_0,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_443,c_1584])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_64,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_406,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_381,c_118])).

cnf(c_9,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_129,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_10223,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X0,X1))),k4_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X1))) ),
    inference(superposition,[status(thm)],[c_406,c_129])).

cnf(c_10402,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X0,X1))),k4_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_10223,c_406])).

cnf(c_732,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_218,c_701])).

cnf(c_1126,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_732])).

cnf(c_1295,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1126,c_381])).

cnf(c_1317,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1295,c_117])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_115,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_120,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_115,c_8])).

cnf(c_4398,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_2,c_120])).

cnf(c_4693,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4398,c_118])).

cnf(c_5415,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4693,c_218])).

cnf(c_5428,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_5415,c_6,c_701,c_1317])).

cnf(c_5442,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_5428])).

cnf(c_5733,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,k2_xboole_0(X3,X1))),X1) ),
    inference(superposition,[status(thm)],[c_5442,c_9])).

cnf(c_10403,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X0,X1))),X1),X2) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_10402,c_6,c_1317,c_5733])).

cnf(c_716,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_701])).

cnf(c_808,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_218,c_742])).

cnf(c_5689,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
    inference(superposition,[status(thm)],[c_808,c_5442])).

cnf(c_6353,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_716,c_5689])).

cnf(c_10404,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_10403,c_6353])).

cnf(c_11109,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(demodulation,[status(thm)],[c_10981,c_64,c_10404])).

cnf(c_6319,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_732,c_716])).

cnf(c_723,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_381,c_701])).

cnf(c_1089,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_723])).

cnf(c_6395,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_6319,c_122,c_1089])).

cnf(c_108,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_47,c_8])).

cnf(c_123,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_108,c_8,c_77])).

cnf(c_358,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_123])).

cnf(c_713,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_701])).

cnf(c_975,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_358,c_713])).

cnf(c_997,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_975,c_8])).

cnf(c_998,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_997,c_4])).

cnf(c_8416,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6395,c_998])).

cnf(c_8517,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_8416,c_6395])).

cnf(c_11110,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_11109,c_8517])).

cnf(c_11476,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_11110,c_1089])).

cnf(c_792,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_742])).

cnf(c_7095,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_792,c_6395])).

cnf(c_7175,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_7095,c_6395])).

cnf(c_11557,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_11476,c_7175])).

cnf(c_140,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X2,X3)),X1) ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_19092,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X3,X2)),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_11557,c_140])).

cnf(c_143,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_7])).

cnf(c_148,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_143,c_8])).

cnf(c_110,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_8,c_8])).

cnf(c_121,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_110,c_8])).

cnf(c_6556,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_792,c_121])).

cnf(c_968,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_118,c_713])).

cnf(c_1006,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_968,c_6])).

cnf(c_6569,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_6556,c_1006])).

cnf(c_25395,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_148,c_6569])).

cnf(c_144,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_25645,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X3),k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_25395,c_144])).

cnf(c_318,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_81,c_118])).

cnf(c_10976,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_318,c_1584])).

cnf(c_312,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_118])).

cnf(c_10224,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0))),k4_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_312,c_129])).

cnf(c_5718,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X0)))) ),
    inference(superposition,[status(thm)],[c_5442,c_9])).

cnf(c_10400,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)))),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_10224,c_6,c_312,c_1317,c_5718])).

cnf(c_10401,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_10400,c_6353])).

cnf(c_11116,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_10976,c_64,c_10401])).

cnf(c_11117,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_11116,c_8517])).

cnf(c_19093,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X3,X2)),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_11117,c_140])).

cnf(c_25682,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X3),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X3,k4_xboole_0(X0,X2)),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_25645,c_19093])).

cnf(c_136,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_25651,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X1),k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_25395,c_136])).

cnf(c_133,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),X2) ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_13115,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_11557,c_133])).

cnf(c_25671,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X1),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_25651,c_13115])).

cnf(c_25683,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X0),X2),k4_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_25682,c_25671])).

cnf(c_141,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_47,c_9])).

cnf(c_150,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_141,c_4])).

cnf(c_11435,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_150,c_11110])).

cnf(c_11598,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_11435,c_11110])).

cnf(c_8401,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_0,c_998])).

cnf(c_30538,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X3),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_11598,c_8401])).

cnf(c_969,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_123,c_713])).

cnf(c_1004,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_969,c_8])).

cnf(c_1005,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_1004,c_4])).

cnf(c_30541,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X3),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) ),
    inference(superposition,[status(thm)],[c_11598,c_1005])).

cnf(c_30629,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X3),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_30541,c_11598])).

cnf(c_30632,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_30538,c_30629])).

cnf(c_44679,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(k4_xboole_0(X1,X3),X0) ),
    inference(superposition,[status(thm)],[c_140,c_30632])).

cnf(c_48271,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_48270,c_19092,c_25683,c_44679])).

cnf(c_48272,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_48271,c_150])).

cnf(c_48273,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_48272])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:47:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.71/1.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.71/1.97  
% 11.71/1.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.71/1.97  
% 11.71/1.97  ------  iProver source info
% 11.71/1.97  
% 11.71/1.97  git: date: 2020-06-30 10:37:57 +0100
% 11.71/1.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.71/1.97  git: non_committed_changes: false
% 11.71/1.97  git: last_make_outside_of_git: false
% 11.71/1.97  
% 11.71/1.97  ------ 
% 11.71/1.97  
% 11.71/1.97  ------ Input Options
% 11.71/1.97  
% 11.71/1.97  --out_options                           all
% 11.71/1.97  --tptp_safe_out                         true
% 11.71/1.97  --problem_path                          ""
% 11.71/1.97  --include_path                          ""
% 11.71/1.97  --clausifier                            res/vclausify_rel
% 11.71/1.97  --clausifier_options                    --mode clausify
% 11.71/1.97  --stdin                                 false
% 11.71/1.97  --stats_out                             all
% 11.71/1.97  
% 11.71/1.97  ------ General Options
% 11.71/1.97  
% 11.71/1.97  --fof                                   false
% 11.71/1.97  --time_out_real                         305.
% 11.71/1.97  --time_out_virtual                      -1.
% 11.71/1.97  --symbol_type_check                     false
% 11.71/1.97  --clausify_out                          false
% 11.71/1.97  --sig_cnt_out                           false
% 11.71/1.97  --trig_cnt_out                          false
% 11.71/1.97  --trig_cnt_out_tolerance                1.
% 11.71/1.97  --trig_cnt_out_sk_spl                   false
% 11.71/1.97  --abstr_cl_out                          false
% 11.71/1.97  
% 11.71/1.97  ------ Global Options
% 11.71/1.97  
% 11.71/1.97  --schedule                              default
% 11.71/1.97  --add_important_lit                     false
% 11.71/1.97  --prop_solver_per_cl                    1000
% 11.71/1.97  --min_unsat_core                        false
% 11.71/1.97  --soft_assumptions                      false
% 11.71/1.97  --soft_lemma_size                       3
% 11.71/1.97  --prop_impl_unit_size                   0
% 11.71/1.97  --prop_impl_unit                        []
% 11.71/1.97  --share_sel_clauses                     true
% 11.71/1.97  --reset_solvers                         false
% 11.71/1.97  --bc_imp_inh                            [conj_cone]
% 11.71/1.97  --conj_cone_tolerance                   3.
% 11.71/1.97  --extra_neg_conj                        none
% 11.71/1.97  --large_theory_mode                     true
% 11.71/1.97  --prolific_symb_bound                   200
% 11.71/1.97  --lt_threshold                          2000
% 11.71/1.97  --clause_weak_htbl                      true
% 11.71/1.97  --gc_record_bc_elim                     false
% 11.71/1.97  
% 11.71/1.97  ------ Preprocessing Options
% 11.71/1.97  
% 11.71/1.97  --preprocessing_flag                    true
% 11.71/1.97  --time_out_prep_mult                    0.1
% 11.71/1.97  --splitting_mode                        input
% 11.71/1.97  --splitting_grd                         true
% 11.71/1.97  --splitting_cvd                         false
% 11.71/1.97  --splitting_cvd_svl                     false
% 11.71/1.97  --splitting_nvd                         32
% 11.71/1.97  --sub_typing                            true
% 11.71/1.97  --prep_gs_sim                           true
% 11.71/1.97  --prep_unflatten                        true
% 11.71/1.97  --prep_res_sim                          true
% 11.71/1.97  --prep_upred                            true
% 11.71/1.97  --prep_sem_filter                       exhaustive
% 11.71/1.97  --prep_sem_filter_out                   false
% 11.71/1.97  --pred_elim                             true
% 11.71/1.97  --res_sim_input                         true
% 11.71/1.97  --eq_ax_congr_red                       true
% 11.71/1.97  --pure_diseq_elim                       true
% 11.71/1.97  --brand_transform                       false
% 11.71/1.97  --non_eq_to_eq                          false
% 11.71/1.97  --prep_def_merge                        true
% 11.71/1.97  --prep_def_merge_prop_impl              false
% 11.71/1.97  --prep_def_merge_mbd                    true
% 11.71/1.97  --prep_def_merge_tr_red                 false
% 11.71/1.97  --prep_def_merge_tr_cl                  false
% 11.71/1.97  --smt_preprocessing                     true
% 11.71/1.97  --smt_ac_axioms                         fast
% 11.71/1.97  --preprocessed_out                      false
% 11.71/1.97  --preprocessed_stats                    false
% 11.71/1.97  
% 11.71/1.97  ------ Abstraction refinement Options
% 11.71/1.97  
% 11.71/1.97  --abstr_ref                             []
% 11.71/1.97  --abstr_ref_prep                        false
% 11.71/1.97  --abstr_ref_until_sat                   false
% 11.71/1.97  --abstr_ref_sig_restrict                funpre
% 11.71/1.97  --abstr_ref_af_restrict_to_split_sk     false
% 11.71/1.97  --abstr_ref_under                       []
% 11.71/1.97  
% 11.71/1.97  ------ SAT Options
% 11.71/1.97  
% 11.71/1.97  --sat_mode                              false
% 11.71/1.97  --sat_fm_restart_options                ""
% 11.71/1.97  --sat_gr_def                            false
% 11.71/1.97  --sat_epr_types                         true
% 11.71/1.97  --sat_non_cyclic_types                  false
% 11.71/1.97  --sat_finite_models                     false
% 11.71/1.97  --sat_fm_lemmas                         false
% 11.71/1.97  --sat_fm_prep                           false
% 11.71/1.97  --sat_fm_uc_incr                        true
% 11.71/1.97  --sat_out_model                         small
% 11.71/1.97  --sat_out_clauses                       false
% 11.71/1.97  
% 11.71/1.97  ------ QBF Options
% 11.71/1.97  
% 11.71/1.97  --qbf_mode                              false
% 11.71/1.97  --qbf_elim_univ                         false
% 11.71/1.97  --qbf_dom_inst                          none
% 11.71/1.97  --qbf_dom_pre_inst                      false
% 11.71/1.97  --qbf_sk_in                             false
% 11.71/1.97  --qbf_pred_elim                         true
% 11.71/1.97  --qbf_split                             512
% 11.71/1.97  
% 11.71/1.97  ------ BMC1 Options
% 11.71/1.97  
% 11.71/1.97  --bmc1_incremental                      false
% 11.71/1.97  --bmc1_axioms                           reachable_all
% 11.71/1.97  --bmc1_min_bound                        0
% 11.71/1.97  --bmc1_max_bound                        -1
% 11.71/1.97  --bmc1_max_bound_default                -1
% 11.71/1.97  --bmc1_symbol_reachability              true
% 11.71/1.97  --bmc1_property_lemmas                  false
% 11.71/1.97  --bmc1_k_induction                      false
% 11.71/1.97  --bmc1_non_equiv_states                 false
% 11.71/1.97  --bmc1_deadlock                         false
% 11.71/1.97  --bmc1_ucm                              false
% 11.71/1.97  --bmc1_add_unsat_core                   none
% 11.71/1.97  --bmc1_unsat_core_children              false
% 11.71/1.97  --bmc1_unsat_core_extrapolate_axioms    false
% 11.71/1.97  --bmc1_out_stat                         full
% 11.71/1.97  --bmc1_ground_init                      false
% 11.71/1.97  --bmc1_pre_inst_next_state              false
% 11.71/1.97  --bmc1_pre_inst_state                   false
% 11.71/1.97  --bmc1_pre_inst_reach_state             false
% 11.71/1.97  --bmc1_out_unsat_core                   false
% 11.71/1.97  --bmc1_aig_witness_out                  false
% 11.71/1.97  --bmc1_verbose                          false
% 11.71/1.97  --bmc1_dump_clauses_tptp                false
% 11.71/1.97  --bmc1_dump_unsat_core_tptp             false
% 11.71/1.97  --bmc1_dump_file                        -
% 11.71/1.97  --bmc1_ucm_expand_uc_limit              128
% 11.71/1.97  --bmc1_ucm_n_expand_iterations          6
% 11.71/1.97  --bmc1_ucm_extend_mode                  1
% 11.71/1.97  --bmc1_ucm_init_mode                    2
% 11.71/1.97  --bmc1_ucm_cone_mode                    none
% 11.71/1.97  --bmc1_ucm_reduced_relation_type        0
% 11.71/1.97  --bmc1_ucm_relax_model                  4
% 11.71/1.97  --bmc1_ucm_full_tr_after_sat            true
% 11.71/1.97  --bmc1_ucm_expand_neg_assumptions       false
% 11.71/1.97  --bmc1_ucm_layered_model                none
% 11.71/1.98  --bmc1_ucm_max_lemma_size               10
% 11.71/1.98  
% 11.71/1.98  ------ AIG Options
% 11.71/1.98  
% 11.71/1.98  --aig_mode                              false
% 11.71/1.98  
% 11.71/1.98  ------ Instantiation Options
% 11.71/1.98  
% 11.71/1.98  --instantiation_flag                    true
% 11.71/1.98  --inst_sos_flag                         false
% 11.71/1.98  --inst_sos_phase                        true
% 11.71/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.71/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.71/1.98  --inst_lit_sel_side                     num_symb
% 11.71/1.98  --inst_solver_per_active                1400
% 11.71/1.98  --inst_solver_calls_frac                1.
% 11.71/1.98  --inst_passive_queue_type               priority_queues
% 11.71/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.71/1.98  --inst_passive_queues_freq              [25;2]
% 11.71/1.98  --inst_dismatching                      true
% 11.71/1.98  --inst_eager_unprocessed_to_passive     true
% 11.71/1.98  --inst_prop_sim_given                   true
% 11.71/1.98  --inst_prop_sim_new                     false
% 11.71/1.98  --inst_subs_new                         false
% 11.71/1.98  --inst_eq_res_simp                      false
% 11.71/1.98  --inst_subs_given                       false
% 11.71/1.98  --inst_orphan_elimination               true
% 11.71/1.98  --inst_learning_loop_flag               true
% 11.71/1.98  --inst_learning_start                   3000
% 11.71/1.98  --inst_learning_factor                  2
% 11.71/1.98  --inst_start_prop_sim_after_learn       3
% 11.71/1.98  --inst_sel_renew                        solver
% 11.71/1.98  --inst_lit_activity_flag                true
% 11.71/1.98  --inst_restr_to_given                   false
% 11.71/1.98  --inst_activity_threshold               500
% 11.71/1.98  --inst_out_proof                        true
% 11.71/1.98  
% 11.71/1.98  ------ Resolution Options
% 11.71/1.98  
% 11.71/1.98  --resolution_flag                       true
% 11.71/1.98  --res_lit_sel                           adaptive
% 11.71/1.98  --res_lit_sel_side                      none
% 11.71/1.98  --res_ordering                          kbo
% 11.71/1.98  --res_to_prop_solver                    active
% 11.71/1.98  --res_prop_simpl_new                    false
% 11.71/1.98  --res_prop_simpl_given                  true
% 11.71/1.98  --res_passive_queue_type                priority_queues
% 11.71/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.71/1.98  --res_passive_queues_freq               [15;5]
% 11.71/1.98  --res_forward_subs                      full
% 11.71/1.98  --res_backward_subs                     full
% 11.71/1.98  --res_forward_subs_resolution           true
% 11.71/1.98  --res_backward_subs_resolution          true
% 11.71/1.98  --res_orphan_elimination                true
% 11.71/1.98  --res_time_limit                        2.
% 11.71/1.98  --res_out_proof                         true
% 11.71/1.98  
% 11.71/1.98  ------ Superposition Options
% 11.71/1.98  
% 11.71/1.98  --superposition_flag                    true
% 11.71/1.98  --sup_passive_queue_type                priority_queues
% 11.71/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.71/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.71/1.98  --demod_completeness_check              fast
% 11.71/1.98  --demod_use_ground                      true
% 11.71/1.98  --sup_to_prop_solver                    passive
% 11.71/1.98  --sup_prop_simpl_new                    true
% 11.71/1.98  --sup_prop_simpl_given                  true
% 11.71/1.98  --sup_fun_splitting                     false
% 11.71/1.98  --sup_smt_interval                      50000
% 11.71/1.98  
% 11.71/1.98  ------ Superposition Simplification Setup
% 11.71/1.98  
% 11.71/1.98  --sup_indices_passive                   []
% 11.71/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.71/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.71/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.71/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.71/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.71/1.98  --sup_full_bw                           [BwDemod]
% 11.71/1.98  --sup_immed_triv                        [TrivRules]
% 11.71/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.71/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.71/1.98  --sup_immed_bw_main                     []
% 11.71/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.71/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.71/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.71/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.71/1.98  
% 11.71/1.98  ------ Combination Options
% 11.71/1.98  
% 11.71/1.98  --comb_res_mult                         3
% 11.71/1.98  --comb_sup_mult                         2
% 11.71/1.98  --comb_inst_mult                        10
% 11.71/1.98  
% 11.71/1.98  ------ Debug Options
% 11.71/1.98  
% 11.71/1.98  --dbg_backtrace                         false
% 11.71/1.98  --dbg_dump_prop_clauses                 false
% 11.71/1.98  --dbg_dump_prop_clauses_file            -
% 11.71/1.98  --dbg_out_stat                          false
% 11.71/1.98  ------ Parsing...
% 11.71/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.71/1.98  
% 11.71/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.71/1.98  
% 11.71/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.71/1.98  
% 11.71/1.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.71/1.98  ------ Proving...
% 11.71/1.98  ------ Problem Properties 
% 11.71/1.98  
% 11.71/1.98  
% 11.71/1.98  clauses                                 10
% 11.71/1.98  conjectures                             1
% 11.71/1.98  EPR                                     0
% 11.71/1.98  Horn                                    10
% 11.71/1.98  unary                                   10
% 11.71/1.98  binary                                  0
% 11.71/1.98  lits                                    10
% 11.71/1.98  lits eq                                 10
% 11.71/1.98  fd_pure                                 0
% 11.71/1.98  fd_pseudo                               0
% 11.71/1.98  fd_cond                                 0
% 11.71/1.98  fd_pseudo_cond                          0
% 11.71/1.98  AC symbols                              0
% 11.71/1.98  
% 11.71/1.98  ------ Schedule UEQ
% 11.71/1.98  
% 11.71/1.98  ------ pure equality problem: resolution off 
% 11.71/1.98  
% 11.71/1.98  ------ Option_UEQ Time Limit: Unbounded
% 11.71/1.98  
% 11.71/1.98  
% 11.71/1.98  ------ 
% 11.71/1.98  Current options:
% 11.71/1.98  ------ 
% 11.71/1.98  
% 11.71/1.98  ------ Input Options
% 11.71/1.98  
% 11.71/1.98  --out_options                           all
% 11.71/1.98  --tptp_safe_out                         true
% 11.71/1.98  --problem_path                          ""
% 11.71/1.98  --include_path                          ""
% 11.71/1.98  --clausifier                            res/vclausify_rel
% 11.71/1.98  --clausifier_options                    --mode clausify
% 11.71/1.98  --stdin                                 false
% 11.71/1.98  --stats_out                             all
% 11.71/1.98  
% 11.71/1.98  ------ General Options
% 11.71/1.98  
% 11.71/1.98  --fof                                   false
% 11.71/1.98  --time_out_real                         305.
% 11.71/1.98  --time_out_virtual                      -1.
% 11.71/1.98  --symbol_type_check                     false
% 11.71/1.98  --clausify_out                          false
% 11.71/1.98  --sig_cnt_out                           false
% 11.71/1.98  --trig_cnt_out                          false
% 11.71/1.98  --trig_cnt_out_tolerance                1.
% 11.71/1.98  --trig_cnt_out_sk_spl                   false
% 11.71/1.98  --abstr_cl_out                          false
% 11.71/1.98  
% 11.71/1.98  ------ Global Options
% 11.71/1.98  
% 11.71/1.98  --schedule                              default
% 11.71/1.98  --add_important_lit                     false
% 11.71/1.98  --prop_solver_per_cl                    1000
% 11.71/1.98  --min_unsat_core                        false
% 11.71/1.98  --soft_assumptions                      false
% 11.71/1.98  --soft_lemma_size                       3
% 11.71/1.98  --prop_impl_unit_size                   0
% 11.71/1.98  --prop_impl_unit                        []
% 11.71/1.98  --share_sel_clauses                     true
% 11.71/1.98  --reset_solvers                         false
% 11.71/1.98  --bc_imp_inh                            [conj_cone]
% 11.71/1.98  --conj_cone_tolerance                   3.
% 11.71/1.98  --extra_neg_conj                        none
% 11.71/1.98  --large_theory_mode                     true
% 11.71/1.98  --prolific_symb_bound                   200
% 11.71/1.98  --lt_threshold                          2000
% 11.71/1.98  --clause_weak_htbl                      true
% 11.71/1.98  --gc_record_bc_elim                     false
% 11.71/1.98  
% 11.71/1.98  ------ Preprocessing Options
% 11.71/1.98  
% 11.71/1.98  --preprocessing_flag                    true
% 11.71/1.98  --time_out_prep_mult                    0.1
% 11.71/1.98  --splitting_mode                        input
% 11.71/1.98  --splitting_grd                         true
% 11.71/1.98  --splitting_cvd                         false
% 11.71/1.98  --splitting_cvd_svl                     false
% 11.71/1.98  --splitting_nvd                         32
% 11.71/1.98  --sub_typing                            true
% 11.71/1.98  --prep_gs_sim                           true
% 11.71/1.98  --prep_unflatten                        true
% 11.71/1.98  --prep_res_sim                          true
% 11.71/1.98  --prep_upred                            true
% 11.71/1.98  --prep_sem_filter                       exhaustive
% 11.71/1.98  --prep_sem_filter_out                   false
% 11.71/1.98  --pred_elim                             true
% 11.71/1.98  --res_sim_input                         true
% 11.71/1.98  --eq_ax_congr_red                       true
% 11.71/1.98  --pure_diseq_elim                       true
% 11.71/1.98  --brand_transform                       false
% 11.71/1.98  --non_eq_to_eq                          false
% 11.71/1.98  --prep_def_merge                        true
% 11.71/1.98  --prep_def_merge_prop_impl              false
% 11.71/1.98  --prep_def_merge_mbd                    true
% 11.71/1.98  --prep_def_merge_tr_red                 false
% 11.71/1.98  --prep_def_merge_tr_cl                  false
% 11.71/1.98  --smt_preprocessing                     true
% 11.71/1.98  --smt_ac_axioms                         fast
% 11.71/1.98  --preprocessed_out                      false
% 11.71/1.98  --preprocessed_stats                    false
% 11.71/1.98  
% 11.71/1.98  ------ Abstraction refinement Options
% 11.71/1.98  
% 11.71/1.98  --abstr_ref                             []
% 11.71/1.98  --abstr_ref_prep                        false
% 11.71/1.98  --abstr_ref_until_sat                   false
% 11.71/1.98  --abstr_ref_sig_restrict                funpre
% 11.71/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.71/1.98  --abstr_ref_under                       []
% 11.71/1.98  
% 11.71/1.98  ------ SAT Options
% 11.71/1.98  
% 11.71/1.98  --sat_mode                              false
% 11.71/1.98  --sat_fm_restart_options                ""
% 11.71/1.98  --sat_gr_def                            false
% 11.71/1.98  --sat_epr_types                         true
% 11.71/1.98  --sat_non_cyclic_types                  false
% 11.71/1.98  --sat_finite_models                     false
% 11.71/1.98  --sat_fm_lemmas                         false
% 11.71/1.98  --sat_fm_prep                           false
% 11.71/1.98  --sat_fm_uc_incr                        true
% 11.71/1.98  --sat_out_model                         small
% 11.71/1.98  --sat_out_clauses                       false
% 11.71/1.98  
% 11.71/1.98  ------ QBF Options
% 11.71/1.98  
% 11.71/1.98  --qbf_mode                              false
% 11.71/1.98  --qbf_elim_univ                         false
% 11.71/1.98  --qbf_dom_inst                          none
% 11.71/1.98  --qbf_dom_pre_inst                      false
% 11.71/1.98  --qbf_sk_in                             false
% 11.71/1.98  --qbf_pred_elim                         true
% 11.71/1.98  --qbf_split                             512
% 11.71/1.98  
% 11.71/1.98  ------ BMC1 Options
% 11.71/1.98  
% 11.71/1.98  --bmc1_incremental                      false
% 11.71/1.98  --bmc1_axioms                           reachable_all
% 11.71/1.98  --bmc1_min_bound                        0
% 11.71/1.98  --bmc1_max_bound                        -1
% 11.71/1.98  --bmc1_max_bound_default                -1
% 11.71/1.98  --bmc1_symbol_reachability              true
% 11.71/1.98  --bmc1_property_lemmas                  false
% 11.71/1.98  --bmc1_k_induction                      false
% 11.71/1.98  --bmc1_non_equiv_states                 false
% 11.71/1.98  --bmc1_deadlock                         false
% 11.71/1.98  --bmc1_ucm                              false
% 11.71/1.98  --bmc1_add_unsat_core                   none
% 11.71/1.98  --bmc1_unsat_core_children              false
% 11.71/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.71/1.98  --bmc1_out_stat                         full
% 11.71/1.98  --bmc1_ground_init                      false
% 11.71/1.98  --bmc1_pre_inst_next_state              false
% 11.71/1.98  --bmc1_pre_inst_state                   false
% 11.71/1.98  --bmc1_pre_inst_reach_state             false
% 11.71/1.98  --bmc1_out_unsat_core                   false
% 11.71/1.98  --bmc1_aig_witness_out                  false
% 11.71/1.98  --bmc1_verbose                          false
% 11.71/1.98  --bmc1_dump_clauses_tptp                false
% 11.71/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.71/1.98  --bmc1_dump_file                        -
% 11.71/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.71/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.71/1.98  --bmc1_ucm_extend_mode                  1
% 11.71/1.98  --bmc1_ucm_init_mode                    2
% 11.71/1.98  --bmc1_ucm_cone_mode                    none
% 11.71/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.71/1.98  --bmc1_ucm_relax_model                  4
% 11.71/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.71/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.71/1.98  --bmc1_ucm_layered_model                none
% 11.71/1.98  --bmc1_ucm_max_lemma_size               10
% 11.71/1.98  
% 11.71/1.98  ------ AIG Options
% 11.71/1.98  
% 11.71/1.98  --aig_mode                              false
% 11.71/1.98  
% 11.71/1.98  ------ Instantiation Options
% 11.71/1.98  
% 11.71/1.98  --instantiation_flag                    false
% 11.71/1.98  --inst_sos_flag                         false
% 11.71/1.98  --inst_sos_phase                        true
% 11.71/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.71/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.71/1.98  --inst_lit_sel_side                     num_symb
% 11.71/1.98  --inst_solver_per_active                1400
% 11.71/1.98  --inst_solver_calls_frac                1.
% 11.71/1.98  --inst_passive_queue_type               priority_queues
% 11.71/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.71/1.98  --inst_passive_queues_freq              [25;2]
% 11.71/1.98  --inst_dismatching                      true
% 11.71/1.98  --inst_eager_unprocessed_to_passive     true
% 11.71/1.98  --inst_prop_sim_given                   true
% 11.71/1.98  --inst_prop_sim_new                     false
% 11.71/1.98  --inst_subs_new                         false
% 11.71/1.98  --inst_eq_res_simp                      false
% 11.71/1.98  --inst_subs_given                       false
% 11.71/1.98  --inst_orphan_elimination               true
% 11.71/1.98  --inst_learning_loop_flag               true
% 11.71/1.98  --inst_learning_start                   3000
% 11.71/1.98  --inst_learning_factor                  2
% 11.71/1.98  --inst_start_prop_sim_after_learn       3
% 11.71/1.98  --inst_sel_renew                        solver
% 11.71/1.98  --inst_lit_activity_flag                true
% 11.71/1.98  --inst_restr_to_given                   false
% 11.71/1.98  --inst_activity_threshold               500
% 11.71/1.98  --inst_out_proof                        true
% 11.71/1.98  
% 11.71/1.98  ------ Resolution Options
% 11.71/1.98  
% 11.71/1.98  --resolution_flag                       false
% 11.71/1.98  --res_lit_sel                           adaptive
% 11.71/1.98  --res_lit_sel_side                      none
% 11.71/1.98  --res_ordering                          kbo
% 11.71/1.98  --res_to_prop_solver                    active
% 11.71/1.98  --res_prop_simpl_new                    false
% 11.71/1.98  --res_prop_simpl_given                  true
% 11.71/1.98  --res_passive_queue_type                priority_queues
% 11.71/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.71/1.98  --res_passive_queues_freq               [15;5]
% 11.71/1.98  --res_forward_subs                      full
% 11.71/1.98  --res_backward_subs                     full
% 11.71/1.98  --res_forward_subs_resolution           true
% 11.71/1.98  --res_backward_subs_resolution          true
% 11.71/1.98  --res_orphan_elimination                true
% 11.71/1.98  --res_time_limit                        2.
% 11.71/1.98  --res_out_proof                         true
% 11.71/1.98  
% 11.71/1.98  ------ Superposition Options
% 11.71/1.98  
% 11.71/1.98  --superposition_flag                    true
% 11.71/1.98  --sup_passive_queue_type                priority_queues
% 11.71/1.98  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.71/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.71/1.98  --demod_completeness_check              fast
% 11.71/1.98  --demod_use_ground                      true
% 11.71/1.98  --sup_to_prop_solver                    active
% 11.71/1.98  --sup_prop_simpl_new                    false
% 11.71/1.98  --sup_prop_simpl_given                  false
% 11.71/1.98  --sup_fun_splitting                     true
% 11.71/1.98  --sup_smt_interval                      10000
% 11.71/1.98  
% 11.71/1.98  ------ Superposition Simplification Setup
% 11.71/1.98  
% 11.71/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.71/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.71/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.71/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.71/1.98  --sup_full_triv                         [TrivRules]
% 11.71/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.71/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.71/1.98  --sup_immed_triv                        [TrivRules]
% 11.71/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.71/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.71/1.98  --sup_immed_bw_main                     []
% 11.71/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.71/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.71/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.71/1.98  --sup_input_bw                          [BwDemod;BwSubsumption]
% 11.71/1.98  
% 11.71/1.98  ------ Combination Options
% 11.71/1.98  
% 11.71/1.98  --comb_res_mult                         1
% 11.71/1.98  --comb_sup_mult                         1
% 11.71/1.98  --comb_inst_mult                        1000000
% 11.71/1.98  
% 11.71/1.98  ------ Debug Options
% 11.71/1.98  
% 11.71/1.98  --dbg_backtrace                         false
% 11.71/1.98  --dbg_dump_prop_clauses                 false
% 11.71/1.98  --dbg_dump_prop_clauses_file            -
% 11.71/1.98  --dbg_out_stat                          false
% 11.71/1.98  
% 11.71/1.98  
% 11.71/1.98  
% 11.71/1.98  
% 11.71/1.98  ------ Proving...
% 11.71/1.98  
% 11.71/1.98  
% 11.71/1.98  % SZS status Theorem for theBenchmark.p
% 11.71/1.98  
% 11.71/1.98   Resolution empty clause
% 11.71/1.98  
% 11.71/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.71/1.98  
% 11.71/1.98  fof(f9,axiom,(
% 11.71/1.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 11.71/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.98  
% 11.71/1.98  fof(f29,plain,(
% 11.71/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 11.71/1.98    inference(cnf_transformation,[],[f9])).
% 11.71/1.98  
% 11.71/1.98  fof(f2,axiom,(
% 11.71/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.71/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.98  
% 11.71/1.98  fof(f22,plain,(
% 11.71/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.71/1.98    inference(cnf_transformation,[],[f2])).
% 11.71/1.98  
% 11.71/1.98  fof(f12,axiom,(
% 11.71/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.71/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.98  
% 11.71/1.98  fof(f32,plain,(
% 11.71/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.71/1.98    inference(cnf_transformation,[],[f12])).
% 11.71/1.98  
% 11.71/1.98  fof(f34,plain,(
% 11.71/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.71/1.98    inference(definition_unfolding,[],[f22,f32,f32])).
% 11.71/1.98  
% 11.71/1.98  fof(f8,axiom,(
% 11.71/1.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.71/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.98  
% 11.71/1.98  fof(f28,plain,(
% 11.71/1.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.71/1.98    inference(cnf_transformation,[],[f8])).
% 11.71/1.98  
% 11.71/1.98  fof(f10,axiom,(
% 11.71/1.98    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.71/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.98  
% 11.71/1.98  fof(f30,plain,(
% 11.71/1.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.71/1.98    inference(cnf_transformation,[],[f10])).
% 11.71/1.98  
% 11.71/1.98  fof(f5,axiom,(
% 11.71/1.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.71/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.98  
% 11.71/1.98  fof(f16,plain,(
% 11.71/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 11.71/1.98    inference(unused_predicate_definition_removal,[],[f5])).
% 11.71/1.98  
% 11.71/1.98  fof(f17,plain,(
% 11.71/1.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 11.71/1.98    inference(ennf_transformation,[],[f16])).
% 11.71/1.98  
% 11.71/1.98  fof(f25,plain,(
% 11.71/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.71/1.98    inference(cnf_transformation,[],[f17])).
% 11.71/1.98  
% 11.71/1.98  fof(f7,axiom,(
% 11.71/1.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.71/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.98  
% 11.71/1.98  fof(f27,plain,(
% 11.71/1.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.71/1.98    inference(cnf_transformation,[],[f7])).
% 11.71/1.98  
% 11.71/1.98  fof(f1,axiom,(
% 11.71/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.71/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.98  
% 11.71/1.98  fof(f21,plain,(
% 11.71/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.71/1.98    inference(cnf_transformation,[],[f1])).
% 11.71/1.98  
% 11.71/1.98  fof(f13,conjecture,(
% 11.71/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.71/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.98  
% 11.71/1.98  fof(f14,negated_conjecture,(
% 11.71/1.98    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.71/1.98    inference(negated_conjecture,[],[f13])).
% 11.71/1.98  
% 11.71/1.98  fof(f18,plain,(
% 11.71/1.98    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.71/1.98    inference(ennf_transformation,[],[f14])).
% 11.71/1.98  
% 11.71/1.98  fof(f19,plain,(
% 11.71/1.98    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.71/1.98    introduced(choice_axiom,[])).
% 11.71/1.98  
% 11.71/1.98  fof(f20,plain,(
% 11.71/1.98    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.71/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 11.71/1.98  
% 11.71/1.98  fof(f33,plain,(
% 11.71/1.98    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.71/1.98    inference(cnf_transformation,[],[f20])).
% 11.71/1.98  
% 11.71/1.98  fof(f3,axiom,(
% 11.71/1.98    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 11.71/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.98  
% 11.71/1.98  fof(f23,plain,(
% 11.71/1.98    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 11.71/1.98    inference(cnf_transformation,[],[f3])).
% 11.71/1.98  
% 11.71/1.98  fof(f35,plain,(
% 11.71/1.98    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 11.71/1.98    inference(definition_unfolding,[],[f33,f32,f23,f23])).
% 11.71/1.98  
% 11.71/1.98  fof(f6,axiom,(
% 11.71/1.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.71/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.98  
% 11.71/1.98  fof(f26,plain,(
% 11.71/1.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.71/1.98    inference(cnf_transformation,[],[f6])).
% 11.71/1.98  
% 11.71/1.98  fof(f11,axiom,(
% 11.71/1.98    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 11.71/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.98  
% 11.71/1.98  fof(f31,plain,(
% 11.71/1.98    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 11.71/1.98    inference(cnf_transformation,[],[f11])).
% 11.71/1.98  
% 11.71/1.98  fof(f4,axiom,(
% 11.71/1.98    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 11.71/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.98  
% 11.71/1.98  fof(f15,plain,(
% 11.71/1.98    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 11.71/1.98    inference(rectify,[],[f4])).
% 11.71/1.98  
% 11.71/1.98  fof(f24,plain,(
% 11.71/1.98    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 11.71/1.98    inference(cnf_transformation,[],[f15])).
% 11.71/1.98  
% 11.71/1.98  cnf(c_7,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.71/1.98      inference(cnf_transformation,[],[f29]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_1,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.71/1.98      inference(cnf_transformation,[],[f34]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_92,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_6,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.71/1.98      inference(cnf_transformation,[],[f28]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_8,plain,
% 11.71/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.71/1.98      inference(cnf_transformation,[],[f30]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_3,plain,
% 11.71/1.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.71/1.98      inference(cnf_transformation,[],[f25]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_5,plain,
% 11.71/1.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.71/1.98      inference(cnf_transformation,[],[f27]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_46,plain,
% 11.71/1.98      ( X0 != X1
% 11.71/1.98      | k4_xboole_0(X0,X2) != X3
% 11.71/1.98      | k4_xboole_0(X3,X1) = k1_xboole_0 ),
% 11.71/1.98      inference(resolution_lifted,[status(thm)],[c_3,c_5]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_47,plain,
% 11.71/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 11.71/1.98      inference(unflattening,[status(thm)],[c_46]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_117,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_8,c_47]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_381,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_92,c_6,c_117]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_409,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_381,c_8]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_0,plain,
% 11.71/1.98      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.71/1.98      inference(cnf_transformation,[],[f21]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_10,negated_conjecture,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.71/1.98      inference(cnf_transformation,[],[f35]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_63,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_0,c_10]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_48270,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_409,c_63]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_81,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_213,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_81,c_1]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_74,plain,
% 11.71/1.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_6,c_47]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_109,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_74,c_8]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_77,plain,
% 11.71/1.98      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_47,c_6]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_122,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_109,c_77]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_218,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 11.71/1.98      inference(light_normalisation,[status(thm)],[c_213,c_6,c_122]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_118,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_8,c_74]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_443,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k1_xboole_0 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_218,c_118]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_103,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_394,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) = X0 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_47,c_381]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_701,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_394,c_6]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_742,plain,
% 11.71/1.98      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_701,c_0]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_1488,plain,
% 11.71/1.98      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = X0 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_103,c_742]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_1584,plain,
% 11.71/1.98      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X2))) = X0 ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_1488,c_8]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_10981,plain,
% 11.71/1.98      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(k1_xboole_0,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_443,c_1584]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_4,plain,
% 11.71/1.98      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.71/1.98      inference(cnf_transformation,[],[f26]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_64,plain,
% 11.71/1.98      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_406,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_381,c_118]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_9,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 11.71/1.98      inference(cnf_transformation,[],[f31]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_129,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X0)) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_10223,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X0,X1))),k4_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X1))) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_406,c_129]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_10402,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X0,X1))),k4_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k1_xboole_0) ),
% 11.71/1.98      inference(light_normalisation,[status(thm)],[c_10223,c_406]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_732,plain,
% 11.71/1.98      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_218,c_701]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_1126,plain,
% 11.71/1.98      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_0,c_732]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_1295,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_1126,c_381]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_1317,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 11.71/1.98      inference(light_normalisation,[status(thm)],[c_1295,c_117]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_2,plain,
% 11.71/1.98      ( k2_xboole_0(X0,X0) = X0 ),
% 11.71/1.98      inference(cnf_transformation,[],[f24]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_115,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_120,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_115,c_8]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_4398,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_2,c_120]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_4693,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_4398,c_118]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_5415,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_4693,c_218]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_5428,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_5415,c_6,c_701,c_1317]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_5442,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_8,c_5428]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_5733,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,k2_xboole_0(X3,X1))),X1) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_5442,c_9]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_10403,plain,
% 11.71/1.98      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X0,X1))),X1),X2) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_10402,c_6,c_1317,c_5733]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_716,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_7,c_701]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_808,plain,
% 11.71/1.98      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_218,c_742]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_5689,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_808,c_5442]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_6353,plain,
% 11.71/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_716,c_5689]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_10404,plain,
% 11.71/1.98      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_10403,c_6353]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_11109,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_10981,c_64,c_10404]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_6319,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_732,c_716]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_723,plain,
% 11.71/1.98      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_381,c_701]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_1089,plain,
% 11.71/1.98      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_0,c_723]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_6395,plain,
% 11.71/1.98      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 11.71/1.98      inference(light_normalisation,[status(thm)],[c_6319,c_122,c_1089]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_108,plain,
% 11.71/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_47,c_8]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_123,plain,
% 11.71/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_108,c_8,c_77]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_358,plain,
% 11.71/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_0,c_123]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_713,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_1,c_701]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_975,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_358,c_713]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_997,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_975,c_8]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_998,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_997,c_4]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_8416,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_6395,c_998]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_8517,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.71/1.98      inference(light_normalisation,[status(thm)],[c_8416,c_6395]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_11110,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 11.71/1.98      inference(light_normalisation,[status(thm)],[c_11109,c_8517]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_11476,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_11110,c_1089]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_792,plain,
% 11.71/1.98      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_7,c_742]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_7095,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_792,c_6395]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_7175,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_7095,c_6395]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_11557,plain,
% 11.71/1.98      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.71/1.98      inference(light_normalisation,[status(thm)],[c_11476,c_7175]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_140,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X2,X3)),X1) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_19092,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X3,X2)),k4_xboole_0(X1,X2)) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_11557,c_140]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_143,plain,
% 11.71/1.98      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_9,c_7]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_148,plain,
% 11.71/1.98      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_143,c_8]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_110,plain,
% 11.71/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_8,c_8]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_121,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_110,c_8]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_6556,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_792,c_121]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_968,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_118,c_713]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_1006,plain,
% 11.71/1.98      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 11.71/1.98      inference(light_normalisation,[status(thm)],[c_968,c_6]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_6569,plain,
% 11.71/1.98      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_6556,c_1006]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_25395,plain,
% 11.71/1.98      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_148,c_6569]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_144,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_25645,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X3),k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_25395,c_144]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_318,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_81,c_118]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_10976,plain,
% 11.71/1.98      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_318,c_1584]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_312,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_7,c_118]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_10224,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0))),k4_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_312,c_129]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_5718,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X0)))) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_5442,c_9]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_10400,plain,
% 11.71/1.98      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)))),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_10224,c_6,c_312,c_1317,c_5718]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_10401,plain,
% 11.71/1.98      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_10400,c_6353]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_11116,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_10976,c_64,c_10401]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_11117,plain,
% 11.71/1.98      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.71/1.98      inference(light_normalisation,[status(thm)],[c_11116,c_8517]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_19093,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X3,X2)),k4_xboole_0(X1,X2)) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_11117,c_140]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_25682,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X3),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X3,k4_xboole_0(X0,X2)),k4_xboole_0(X1,X2)) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_25645,c_19093]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_136,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_25651,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X1),k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_25395,c_136]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_133,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),X2) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_13115,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),k4_xboole_0(X2,X1)) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_11557,c_133]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_25671,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X1),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,X1)) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_25651,c_13115]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_25683,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X0),X2),k4_xboole_0(X2,X0)) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_25682,c_25671]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_141,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_47,c_9]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_150,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_141,c_4]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_11435,plain,
% 11.71/1.98      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_150,c_11110]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_11598,plain,
% 11.71/1.98      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(X0,X1) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_11435,c_11110]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_8401,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_0,c_998]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_30538,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X3),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_11598,c_8401]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_969,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_123,c_713]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_1004,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_969,c_8]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_1005,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_1004,c_4]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_30541,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X3),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_11598,c_1005]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_30629,plain,
% 11.71/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X3),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_30541,c_11598]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_30632,plain,
% 11.71/1.98      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_30538,c_30629]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_44679,plain,
% 11.71/1.98      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(k4_xboole_0(X1,X3),X0) ),
% 11.71/1.98      inference(superposition,[status(thm)],[c_140,c_30632]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_48271,plain,
% 11.71/1.98      ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_48270,c_19092,c_25683,c_44679]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_48272,plain,
% 11.71/1.98      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.71/1.98      inference(demodulation,[status(thm)],[c_48271,c_150]) ).
% 11.71/1.98  
% 11.71/1.98  cnf(c_48273,plain,
% 11.71/1.98      ( $false ),
% 11.71/1.98      inference(equality_resolution_simp,[status(thm)],[c_48272]) ).
% 11.71/1.98  
% 11.71/1.98  
% 11.71/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.71/1.98  
% 11.71/1.98  ------                               Statistics
% 11.71/1.98  
% 11.71/1.98  ------ General
% 11.71/1.98  
% 11.71/1.98  abstr_ref_over_cycles:                  0
% 11.71/1.98  abstr_ref_under_cycles:                 0
% 11.71/1.98  gc_basic_clause_elim:                   0
% 11.71/1.98  forced_gc_time:                         0
% 11.71/1.98  parsing_time:                           0.016
% 11.71/1.98  unif_index_cands_time:                  0.
% 11.71/1.98  unif_index_add_time:                    0.
% 11.71/1.98  orderings_time:                         0.
% 11.71/1.98  out_proof_time:                         0.008
% 11.71/1.98  total_time:                             1.477
% 11.71/1.98  num_of_symbols:                         39
% 11.71/1.98  num_of_terms:                           77523
% 11.71/1.98  
% 11.71/1.98  ------ Preprocessing
% 11.71/1.98  
% 11.71/1.98  num_of_splits:                          0
% 11.71/1.98  num_of_split_atoms:                     2
% 11.71/1.98  num_of_reused_defs:                     7
% 11.71/1.98  num_eq_ax_congr_red:                    1
% 11.71/1.98  num_of_sem_filtered_clauses:            0
% 11.71/1.98  num_of_subtypes:                        0
% 11.71/1.98  monotx_restored_types:                  0
% 11.71/1.98  sat_num_of_epr_types:                   0
% 11.71/1.98  sat_num_of_non_cyclic_types:            0
% 11.71/1.98  sat_guarded_non_collapsed_types:        0
% 11.71/1.98  num_pure_diseq_elim:                    0
% 11.71/1.98  simp_replaced_by:                       0
% 11.71/1.98  res_preprocessed:                       35
% 11.71/1.98  prep_upred:                             0
% 11.71/1.98  prep_unflattend:                        2
% 11.71/1.98  smt_new_axioms:                         0
% 11.71/1.98  pred_elim_cands:                        0
% 11.71/1.98  pred_elim:                              1
% 11.71/1.98  pred_elim_cl:                           1
% 11.71/1.98  pred_elim_cycles:                       2
% 11.71/1.98  merged_defs:                            0
% 11.71/1.98  merged_defs_ncl:                        0
% 11.71/1.98  bin_hyper_res:                          0
% 11.71/1.98  prep_cycles:                            3
% 11.71/1.98  pred_elim_time:                         0.
% 11.71/1.98  splitting_time:                         0.
% 11.71/1.98  sem_filter_time:                        0.
% 11.71/1.98  monotx_time:                            0.
% 11.71/1.98  subtype_inf_time:                       0.
% 11.71/1.98  
% 11.71/1.98  ------ Problem properties
% 11.71/1.98  
% 11.71/1.98  clauses:                                10
% 11.71/1.98  conjectures:                            1
% 11.71/1.98  epr:                                    0
% 11.71/1.98  horn:                                   10
% 11.71/1.98  ground:                                 1
% 11.71/1.98  unary:                                  10
% 11.71/1.98  binary:                                 0
% 11.71/1.98  lits:                                   10
% 11.71/1.98  lits_eq:                                10
% 11.71/1.98  fd_pure:                                0
% 11.71/1.98  fd_pseudo:                              0
% 11.71/1.98  fd_cond:                                0
% 11.71/1.98  fd_pseudo_cond:                         0
% 11.71/1.98  ac_symbols:                             1
% 11.71/1.98  
% 11.71/1.98  ------ Propositional Solver
% 11.71/1.98  
% 11.71/1.98  prop_solver_calls:                      17
% 11.71/1.98  prop_fast_solver_calls:                 85
% 11.71/1.98  smt_solver_calls:                       0
% 11.71/1.98  smt_fast_solver_calls:                  0
% 11.71/1.98  prop_num_of_clauses:                    333
% 11.71/1.98  prop_preprocess_simplified:             578
% 11.71/1.98  prop_fo_subsumed:                       0
% 11.71/1.98  prop_solver_time:                       0.
% 11.71/1.98  smt_solver_time:                        0.
% 11.71/1.98  smt_fast_solver_time:                   0.
% 11.71/1.98  prop_fast_solver_time:                  0.
% 11.71/1.98  prop_unsat_core_time:                   0.
% 11.71/1.98  
% 11.71/1.98  ------ QBF
% 11.71/1.98  
% 11.71/1.98  qbf_q_res:                              0
% 11.71/1.98  qbf_num_tautologies:                    0
% 11.71/1.98  qbf_prep_cycles:                        0
% 11.71/1.98  
% 11.71/1.98  ------ BMC1
% 11.71/1.98  
% 11.71/1.98  bmc1_current_bound:                     -1
% 11.71/1.98  bmc1_last_solved_bound:                 -1
% 11.71/1.98  bmc1_unsat_core_size:                   -1
% 11.71/1.98  bmc1_unsat_core_parents_size:           -1
% 11.71/1.98  bmc1_merge_next_fun:                    0
% 11.71/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.71/1.98  
% 11.71/1.98  ------ Instantiation
% 11.71/1.98  
% 11.71/1.98  inst_num_of_clauses:                    0
% 11.71/1.98  inst_num_in_passive:                    0
% 11.71/1.98  inst_num_in_active:                     0
% 11.71/1.98  inst_num_in_unprocessed:                0
% 11.71/1.98  inst_num_of_loops:                      0
% 11.71/1.98  inst_num_of_learning_restarts:          0
% 11.71/1.98  inst_num_moves_active_passive:          0
% 11.71/1.98  inst_lit_activity:                      0
% 11.71/1.98  inst_lit_activity_moves:                0
% 11.71/1.98  inst_num_tautologies:                   0
% 11.71/1.98  inst_num_prop_implied:                  0
% 11.71/1.98  inst_num_existing_simplified:           0
% 11.71/1.98  inst_num_eq_res_simplified:             0
% 11.71/1.98  inst_num_child_elim:                    0
% 11.71/1.98  inst_num_of_dismatching_blockings:      0
% 11.71/1.98  inst_num_of_non_proper_insts:           0
% 11.71/1.98  inst_num_of_duplicates:                 0
% 11.71/1.98  inst_inst_num_from_inst_to_res:         0
% 11.71/1.98  inst_dismatching_checking_time:         0.
% 11.71/1.98  
% 11.71/1.98  ------ Resolution
% 11.71/1.98  
% 11.71/1.98  res_num_of_clauses:                     0
% 11.71/1.98  res_num_in_passive:                     0
% 11.71/1.98  res_num_in_active:                      0
% 11.71/1.98  res_num_of_loops:                       38
% 11.71/1.98  res_forward_subset_subsumed:            0
% 11.71/1.98  res_backward_subset_subsumed:           0
% 11.71/1.98  res_forward_subsumed:                   0
% 11.71/1.98  res_backward_subsumed:                  0
% 11.71/1.98  res_forward_subsumption_resolution:     0
% 11.71/1.98  res_backward_subsumption_resolution:    0
% 11.71/1.98  res_clause_to_clause_subsumption:       128022
% 11.71/1.98  res_orphan_elimination:                 0
% 11.71/1.98  res_tautology_del:                      0
% 11.71/1.98  res_num_eq_res_simplified:              0
% 11.71/1.98  res_num_sel_changes:                    0
% 11.71/1.98  res_moves_from_active_to_pass:          0
% 11.71/1.98  
% 11.71/1.98  ------ Superposition
% 11.71/1.98  
% 11.71/1.98  sup_time_total:                         0.
% 11.71/1.98  sup_time_generating:                    0.
% 11.71/1.98  sup_time_sim_full:                      0.
% 11.71/1.98  sup_time_sim_immed:                     0.
% 11.71/1.98  
% 11.71/1.98  sup_num_of_clauses:                     5346
% 11.71/1.98  sup_num_in_active:                      152
% 11.71/1.98  sup_num_in_passive:                     5194
% 11.71/1.98  sup_num_of_loops:                       200
% 11.71/1.98  sup_fw_superposition:                   18080
% 11.71/1.98  sup_bw_superposition:                   14941
% 11.71/1.98  sup_immediate_simplified:               14342
% 11.71/1.98  sup_given_eliminated:                   9
% 11.71/1.98  comparisons_done:                       0
% 11.71/1.98  comparisons_avoided:                    0
% 11.71/1.98  
% 11.71/1.98  ------ Simplifications
% 11.71/1.98  
% 11.71/1.98  
% 11.71/1.98  sim_fw_subset_subsumed:                 0
% 11.71/1.98  sim_bw_subset_subsumed:                 0
% 11.71/1.98  sim_fw_subsumed:                        2144
% 11.71/1.98  sim_bw_subsumed:                        72
% 11.71/1.98  sim_fw_subsumption_res:                 0
% 11.71/1.98  sim_bw_subsumption_res:                 0
% 11.71/1.98  sim_tautology_del:                      0
% 11.71/1.98  sim_eq_tautology_del:                   3883
% 11.71/1.98  sim_eq_res_simp:                        0
% 11.71/1.98  sim_fw_demodulated:                     9527
% 11.71/1.98  sim_bw_demodulated:                     194
% 11.71/1.98  sim_light_normalised:                   5248
% 11.71/1.98  sim_joinable_taut:                      86
% 11.71/1.98  sim_joinable_simp:                      0
% 11.71/1.98  sim_ac_normalised:                      0
% 11.71/1.98  sim_smt_subsumption:                    0
% 11.71/1.98  
%------------------------------------------------------------------------------
