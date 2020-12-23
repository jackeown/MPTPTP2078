%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:03 EST 2020

% Result     : Theorem 15.93s
% Output     : CNFRefutation 15.93s
% Verified   : 
% Statistics : Number of formulae       :  133 (5136 expanded)
%              Number of clauses        :  100 (2219 expanded)
%              Number of leaves         :   13 (1207 expanded)
%              Depth                    :   30
%              Number of atoms          :  141 (6600 expanded)
%              Number of equality atoms :  132 (4927 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f31,f31])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

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

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

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

fof(f36,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f33,f31,f23,f23])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

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

cnf(c_74,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_47])).

cnf(c_8,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_128,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_74,c_8])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_135,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_128,c_4])).

cnf(c_311,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_135,c_1])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_108,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_47])).

cnf(c_316,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_311,c_6,c_108])).

cnf(c_557,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_316,c_7])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_10,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_63,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_10])).

cnf(c_49518,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_557,c_63])).

cnf(c_122,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_74,c_8])).

cnf(c_64,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_138,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_122,c_64])).

cnf(c_107,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_74])).

cnf(c_328,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_138,c_107])).

cnf(c_94,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_535,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_47,c_316])).

cnf(c_753,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_535,c_6])).

cnf(c_796,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_753,c_0])).

cnf(c_949,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = X0 ),
    inference(superposition,[status(thm)],[c_94,c_796])).

cnf(c_1038,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X2))) = X0 ),
    inference(demodulation,[status(thm)],[c_949,c_7])).

cnf(c_5979,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_1038])).

cnf(c_18363,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_328,c_5979])).

cnf(c_18588,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_18363,c_6])).

cnf(c_334,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_138,c_1])).

cnf(c_98,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_74,c_7])).

cnf(c_77,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_47,c_6])).

cnf(c_113,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_98,c_77])).

cnf(c_339,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_334,c_6,c_113])).

cnf(c_787,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_339,c_753])).

cnf(c_1482,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_787])).

cnf(c_305,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_135,c_107])).

cnf(c_118,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_8254,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0))),k4_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_305,c_118])).

cnf(c_1657,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1482,c_316])).

cnf(c_1680,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1657,c_108])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_105,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_110,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_105,c_7])).

cnf(c_3425,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_2,c_110])).

cnf(c_3693,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3425,c_107])).

cnf(c_4505,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3693,c_339])).

cnf(c_4521,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_4505,c_6,c_753,c_1680])).

cnf(c_4534,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_4521])).

cnf(c_4803,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X0)))) ),
    inference(superposition,[status(thm)],[c_4534,c_8])).

cnf(c_8405,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)))),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_8254,c_6,c_305,c_1680,c_4803])).

cnf(c_99,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_47,c_7])).

cnf(c_112,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_99,c_7,c_77])).

cnf(c_765,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_753])).

cnf(c_1100,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_112,c_765])).

cnf(c_1137,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_1100,c_7])).

cnf(c_1138,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_1137,c_4])).

cnf(c_869,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_339,c_796])).

cnf(c_4774,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
    inference(superposition,[status(thm)],[c_869,c_4534])).

cnf(c_6418,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X3))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1138,c_4774])).

cnf(c_8406,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_8405,c_6418])).

cnf(c_18589,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_18588,c_1482,c_8406])).

cnf(c_127,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X2,X3)),X1) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_19051,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X3,X2)),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_18589,c_127])).

cnf(c_129,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_47,c_8])).

cnf(c_134,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_129,c_4])).

cnf(c_85,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_47])).

cnf(c_211,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_85,c_7])).

cnf(c_420,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_138,c_211])).

cnf(c_950,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = X1 ),
    inference(superposition,[status(thm)],[c_94,c_753])).

cnf(c_1037,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = X1 ),
    inference(demodulation,[status(thm)],[c_950,c_7])).

cnf(c_5783,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)),X2) = X2 ),
    inference(superposition,[status(thm)],[c_8,c_1037])).

cnf(c_18057,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_420,c_5783])).

cnf(c_18295,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(light_normalisation,[status(thm)],[c_18057,c_6])).

cnf(c_124,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_11382,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(k4_xboole_0(X1,X2),X2))) ),
    inference(superposition,[status(thm)],[c_420,c_124])).

cnf(c_11717,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(k4_xboole_0(X1,X2),X2))) ),
    inference(light_normalisation,[status(thm)],[c_11382,c_6])).

cnf(c_121,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),X2) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_9862,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k2_xboole_0(X2,X4))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X3,k2_xboole_0(X2,X4)))),X2) ),
    inference(superposition,[status(thm)],[c_4774,c_121])).

cnf(c_2784,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_1680,c_8])).

cnf(c_2791,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_2784,c_1680])).

cnf(c_2792,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_2791,c_6])).

cnf(c_10499,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_2792,c_1680])).

cnf(c_11718,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_11717,c_420,c_9862,c_10499])).

cnf(c_123,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_47,c_8])).

cnf(c_137,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_123,c_64])).

cnf(c_2865,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_138,c_137])).

cnf(c_11719,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_11718,c_796,c_2865])).

cnf(c_18296,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_18295,c_1482,c_11719])).

cnf(c_18646,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_134,c_18296])).

cnf(c_18889,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_18646,c_18296])).

cnf(c_33033,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(X0,k4_xboole_0(X1,X3)) ),
    inference(superposition,[status(thm)],[c_127,c_18889])).

cnf(c_49519,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)),k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_49518,c_19051,c_33033])).

cnf(c_49520,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_49519,c_4,c_47])).

cnf(c_50250,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1,c_49520])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.93/2.54  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.93/2.54  
% 15.93/2.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.93/2.54  
% 15.93/2.54  ------  iProver source info
% 15.93/2.54  
% 15.93/2.54  git: date: 2020-06-30 10:37:57 +0100
% 15.93/2.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.93/2.54  git: non_committed_changes: false
% 15.93/2.54  git: last_make_outside_of_git: false
% 15.93/2.54  
% 15.93/2.54  ------ 
% 15.93/2.54  
% 15.93/2.54  ------ Input Options
% 15.93/2.54  
% 15.93/2.54  --out_options                           all
% 15.93/2.54  --tptp_safe_out                         true
% 15.93/2.54  --problem_path                          ""
% 15.93/2.54  --include_path                          ""
% 15.93/2.54  --clausifier                            res/vclausify_rel
% 15.93/2.54  --clausifier_options                    --mode clausify
% 15.93/2.54  --stdin                                 false
% 15.93/2.54  --stats_out                             all
% 15.93/2.54  
% 15.93/2.54  ------ General Options
% 15.93/2.54  
% 15.93/2.54  --fof                                   false
% 15.93/2.54  --time_out_real                         305.
% 15.93/2.54  --time_out_virtual                      -1.
% 15.93/2.54  --symbol_type_check                     false
% 15.93/2.54  --clausify_out                          false
% 15.93/2.54  --sig_cnt_out                           false
% 15.93/2.54  --trig_cnt_out                          false
% 15.93/2.54  --trig_cnt_out_tolerance                1.
% 15.93/2.54  --trig_cnt_out_sk_spl                   false
% 15.93/2.54  --abstr_cl_out                          false
% 15.93/2.54  
% 15.93/2.54  ------ Global Options
% 15.93/2.54  
% 15.93/2.54  --schedule                              default
% 15.93/2.54  --add_important_lit                     false
% 15.93/2.54  --prop_solver_per_cl                    1000
% 15.93/2.54  --min_unsat_core                        false
% 15.93/2.54  --soft_assumptions                      false
% 15.93/2.54  --soft_lemma_size                       3
% 15.93/2.54  --prop_impl_unit_size                   0
% 15.93/2.54  --prop_impl_unit                        []
% 15.93/2.54  --share_sel_clauses                     true
% 15.93/2.54  --reset_solvers                         false
% 15.93/2.54  --bc_imp_inh                            [conj_cone]
% 15.93/2.54  --conj_cone_tolerance                   3.
% 15.93/2.54  --extra_neg_conj                        none
% 15.93/2.54  --large_theory_mode                     true
% 15.93/2.54  --prolific_symb_bound                   200
% 15.93/2.54  --lt_threshold                          2000
% 15.93/2.54  --clause_weak_htbl                      true
% 15.93/2.54  --gc_record_bc_elim                     false
% 15.93/2.55  
% 15.93/2.55  ------ Preprocessing Options
% 15.93/2.55  
% 15.93/2.55  --preprocessing_flag                    true
% 15.93/2.55  --time_out_prep_mult                    0.1
% 15.93/2.55  --splitting_mode                        input
% 15.93/2.55  --splitting_grd                         true
% 15.93/2.55  --splitting_cvd                         false
% 15.93/2.55  --splitting_cvd_svl                     false
% 15.93/2.55  --splitting_nvd                         32
% 15.93/2.55  --sub_typing                            true
% 15.93/2.55  --prep_gs_sim                           true
% 15.93/2.55  --prep_unflatten                        true
% 15.93/2.55  --prep_res_sim                          true
% 15.93/2.55  --prep_upred                            true
% 15.93/2.55  --prep_sem_filter                       exhaustive
% 15.93/2.55  --prep_sem_filter_out                   false
% 15.93/2.55  --pred_elim                             true
% 15.93/2.55  --res_sim_input                         true
% 15.93/2.55  --eq_ax_congr_red                       true
% 15.93/2.55  --pure_diseq_elim                       true
% 15.93/2.55  --brand_transform                       false
% 15.93/2.55  --non_eq_to_eq                          false
% 15.93/2.55  --prep_def_merge                        true
% 15.93/2.55  --prep_def_merge_prop_impl              false
% 15.93/2.55  --prep_def_merge_mbd                    true
% 15.93/2.55  --prep_def_merge_tr_red                 false
% 15.93/2.55  --prep_def_merge_tr_cl                  false
% 15.93/2.55  --smt_preprocessing                     true
% 15.93/2.55  --smt_ac_axioms                         fast
% 15.93/2.55  --preprocessed_out                      false
% 15.93/2.55  --preprocessed_stats                    false
% 15.93/2.55  
% 15.93/2.55  ------ Abstraction refinement Options
% 15.93/2.55  
% 15.93/2.55  --abstr_ref                             []
% 15.93/2.55  --abstr_ref_prep                        false
% 15.93/2.55  --abstr_ref_until_sat                   false
% 15.93/2.55  --abstr_ref_sig_restrict                funpre
% 15.93/2.55  --abstr_ref_af_restrict_to_split_sk     false
% 15.93/2.55  --abstr_ref_under                       []
% 15.93/2.55  
% 15.93/2.55  ------ SAT Options
% 15.93/2.55  
% 15.93/2.55  --sat_mode                              false
% 15.93/2.55  --sat_fm_restart_options                ""
% 15.93/2.55  --sat_gr_def                            false
% 15.93/2.55  --sat_epr_types                         true
% 15.93/2.55  --sat_non_cyclic_types                  false
% 15.93/2.55  --sat_finite_models                     false
% 15.93/2.55  --sat_fm_lemmas                         false
% 15.93/2.55  --sat_fm_prep                           false
% 15.93/2.55  --sat_fm_uc_incr                        true
% 15.93/2.55  --sat_out_model                         small
% 15.93/2.55  --sat_out_clauses                       false
% 15.93/2.55  
% 15.93/2.55  ------ QBF Options
% 15.93/2.55  
% 15.93/2.55  --qbf_mode                              false
% 15.93/2.55  --qbf_elim_univ                         false
% 15.93/2.55  --qbf_dom_inst                          none
% 15.93/2.55  --qbf_dom_pre_inst                      false
% 15.93/2.55  --qbf_sk_in                             false
% 15.93/2.55  --qbf_pred_elim                         true
% 15.93/2.55  --qbf_split                             512
% 15.93/2.55  
% 15.93/2.55  ------ BMC1 Options
% 15.93/2.55  
% 15.93/2.55  --bmc1_incremental                      false
% 15.93/2.55  --bmc1_axioms                           reachable_all
% 15.93/2.55  --bmc1_min_bound                        0
% 15.93/2.55  --bmc1_max_bound                        -1
% 15.93/2.55  --bmc1_max_bound_default                -1
% 15.93/2.55  --bmc1_symbol_reachability              true
% 15.93/2.55  --bmc1_property_lemmas                  false
% 15.93/2.55  --bmc1_k_induction                      false
% 15.93/2.55  --bmc1_non_equiv_states                 false
% 15.93/2.55  --bmc1_deadlock                         false
% 15.93/2.55  --bmc1_ucm                              false
% 15.93/2.55  --bmc1_add_unsat_core                   none
% 15.93/2.55  --bmc1_unsat_core_children              false
% 15.93/2.55  --bmc1_unsat_core_extrapolate_axioms    false
% 15.93/2.55  --bmc1_out_stat                         full
% 15.93/2.55  --bmc1_ground_init                      false
% 15.93/2.55  --bmc1_pre_inst_next_state              false
% 15.93/2.55  --bmc1_pre_inst_state                   false
% 15.93/2.55  --bmc1_pre_inst_reach_state             false
% 15.93/2.55  --bmc1_out_unsat_core                   false
% 15.93/2.55  --bmc1_aig_witness_out                  false
% 15.93/2.55  --bmc1_verbose                          false
% 15.93/2.55  --bmc1_dump_clauses_tptp                false
% 15.93/2.55  --bmc1_dump_unsat_core_tptp             false
% 15.93/2.55  --bmc1_dump_file                        -
% 15.93/2.55  --bmc1_ucm_expand_uc_limit              128
% 15.93/2.55  --bmc1_ucm_n_expand_iterations          6
% 15.93/2.55  --bmc1_ucm_extend_mode                  1
% 15.93/2.55  --bmc1_ucm_init_mode                    2
% 15.93/2.55  --bmc1_ucm_cone_mode                    none
% 15.93/2.55  --bmc1_ucm_reduced_relation_type        0
% 15.93/2.55  --bmc1_ucm_relax_model                  4
% 15.93/2.55  --bmc1_ucm_full_tr_after_sat            true
% 15.93/2.55  --bmc1_ucm_expand_neg_assumptions       false
% 15.93/2.55  --bmc1_ucm_layered_model                none
% 15.93/2.55  --bmc1_ucm_max_lemma_size               10
% 15.93/2.55  
% 15.93/2.55  ------ AIG Options
% 15.93/2.55  
% 15.93/2.55  --aig_mode                              false
% 15.93/2.55  
% 15.93/2.55  ------ Instantiation Options
% 15.93/2.55  
% 15.93/2.55  --instantiation_flag                    true
% 15.93/2.55  --inst_sos_flag                         false
% 15.93/2.55  --inst_sos_phase                        true
% 15.93/2.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.93/2.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.93/2.55  --inst_lit_sel_side                     num_symb
% 15.93/2.55  --inst_solver_per_active                1400
% 15.93/2.55  --inst_solver_calls_frac                1.
% 15.93/2.55  --inst_passive_queue_type               priority_queues
% 15.93/2.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.93/2.55  --inst_passive_queues_freq              [25;2]
% 15.93/2.55  --inst_dismatching                      true
% 15.93/2.55  --inst_eager_unprocessed_to_passive     true
% 15.93/2.55  --inst_prop_sim_given                   true
% 15.93/2.55  --inst_prop_sim_new                     false
% 15.93/2.55  --inst_subs_new                         false
% 15.93/2.55  --inst_eq_res_simp                      false
% 15.93/2.55  --inst_subs_given                       false
% 15.93/2.55  --inst_orphan_elimination               true
% 15.93/2.55  --inst_learning_loop_flag               true
% 15.93/2.55  --inst_learning_start                   3000
% 15.93/2.55  --inst_learning_factor                  2
% 15.93/2.55  --inst_start_prop_sim_after_learn       3
% 15.93/2.55  --inst_sel_renew                        solver
% 15.93/2.55  --inst_lit_activity_flag                true
% 15.93/2.55  --inst_restr_to_given                   false
% 15.93/2.55  --inst_activity_threshold               500
% 15.93/2.55  --inst_out_proof                        true
% 15.93/2.55  
% 15.93/2.55  ------ Resolution Options
% 15.93/2.55  
% 15.93/2.55  --resolution_flag                       true
% 15.93/2.55  --res_lit_sel                           adaptive
% 15.93/2.55  --res_lit_sel_side                      none
% 15.93/2.55  --res_ordering                          kbo
% 15.93/2.55  --res_to_prop_solver                    active
% 15.93/2.55  --res_prop_simpl_new                    false
% 15.93/2.55  --res_prop_simpl_given                  true
% 15.93/2.55  --res_passive_queue_type                priority_queues
% 15.93/2.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.93/2.55  --res_passive_queues_freq               [15;5]
% 15.93/2.55  --res_forward_subs                      full
% 15.93/2.55  --res_backward_subs                     full
% 15.93/2.55  --res_forward_subs_resolution           true
% 15.93/2.55  --res_backward_subs_resolution          true
% 15.93/2.55  --res_orphan_elimination                true
% 15.93/2.55  --res_time_limit                        2.
% 15.93/2.55  --res_out_proof                         true
% 15.93/2.55  
% 15.93/2.55  ------ Superposition Options
% 15.93/2.55  
% 15.93/2.55  --superposition_flag                    true
% 15.93/2.55  --sup_passive_queue_type                priority_queues
% 15.93/2.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.93/2.55  --sup_passive_queues_freq               [8;1;4]
% 15.93/2.55  --demod_completeness_check              fast
% 15.93/2.55  --demod_use_ground                      true
% 15.93/2.55  --sup_to_prop_solver                    passive
% 15.93/2.55  --sup_prop_simpl_new                    true
% 15.93/2.55  --sup_prop_simpl_given                  true
% 15.93/2.55  --sup_fun_splitting                     false
% 15.93/2.55  --sup_smt_interval                      50000
% 15.93/2.55  
% 15.93/2.55  ------ Superposition Simplification Setup
% 15.93/2.55  
% 15.93/2.55  --sup_indices_passive                   []
% 15.93/2.55  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.93/2.55  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.93/2.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.93/2.55  --sup_full_triv                         [TrivRules;PropSubs]
% 15.93/2.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.93/2.55  --sup_full_bw                           [BwDemod]
% 15.93/2.55  --sup_immed_triv                        [TrivRules]
% 15.93/2.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.93/2.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.93/2.55  --sup_immed_bw_main                     []
% 15.93/2.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.93/2.55  --sup_input_triv                        [Unflattening;TrivRules]
% 15.93/2.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.93/2.55  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.93/2.55  
% 15.93/2.55  ------ Combination Options
% 15.93/2.55  
% 15.93/2.55  --comb_res_mult                         3
% 15.93/2.55  --comb_sup_mult                         2
% 15.93/2.55  --comb_inst_mult                        10
% 15.93/2.55  
% 15.93/2.55  ------ Debug Options
% 15.93/2.55  
% 15.93/2.55  --dbg_backtrace                         false
% 15.93/2.55  --dbg_dump_prop_clauses                 false
% 15.93/2.55  --dbg_dump_prop_clauses_file            -
% 15.93/2.55  --dbg_out_stat                          false
% 15.93/2.55  ------ Parsing...
% 15.93/2.55  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.93/2.55  
% 15.93/2.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.93/2.55  
% 15.93/2.55  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.93/2.55  
% 15.93/2.55  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.93/2.55  ------ Proving...
% 15.93/2.55  ------ Problem Properties 
% 15.93/2.55  
% 15.93/2.55  
% 15.93/2.55  clauses                                 10
% 15.93/2.55  conjectures                             1
% 15.93/2.55  EPR                                     0
% 15.93/2.55  Horn                                    10
% 15.93/2.55  unary                                   10
% 15.93/2.55  binary                                  0
% 15.93/2.55  lits                                    10
% 15.93/2.55  lits eq                                 10
% 15.93/2.55  fd_pure                                 0
% 15.93/2.55  fd_pseudo                               0
% 15.93/2.55  fd_cond                                 0
% 15.93/2.55  fd_pseudo_cond                          0
% 15.93/2.55  AC symbols                              0
% 15.93/2.55  
% 15.93/2.55  ------ Schedule UEQ
% 15.93/2.55  
% 15.93/2.55  ------ pure equality problem: resolution off 
% 15.93/2.55  
% 15.93/2.55  ------ Option_UEQ Time Limit: Unbounded
% 15.93/2.55  
% 15.93/2.55  
% 15.93/2.55  ------ 
% 15.93/2.55  Current options:
% 15.93/2.55  ------ 
% 15.93/2.55  
% 15.93/2.55  ------ Input Options
% 15.93/2.55  
% 15.93/2.55  --out_options                           all
% 15.93/2.55  --tptp_safe_out                         true
% 15.93/2.55  --problem_path                          ""
% 15.93/2.55  --include_path                          ""
% 15.93/2.55  --clausifier                            res/vclausify_rel
% 15.93/2.55  --clausifier_options                    --mode clausify
% 15.93/2.55  --stdin                                 false
% 15.93/2.55  --stats_out                             all
% 15.93/2.55  
% 15.93/2.55  ------ General Options
% 15.93/2.55  
% 15.93/2.55  --fof                                   false
% 15.93/2.55  --time_out_real                         305.
% 15.93/2.55  --time_out_virtual                      -1.
% 15.93/2.55  --symbol_type_check                     false
% 15.93/2.55  --clausify_out                          false
% 15.93/2.55  --sig_cnt_out                           false
% 15.93/2.55  --trig_cnt_out                          false
% 15.93/2.55  --trig_cnt_out_tolerance                1.
% 15.93/2.55  --trig_cnt_out_sk_spl                   false
% 15.93/2.55  --abstr_cl_out                          false
% 15.93/2.55  
% 15.93/2.55  ------ Global Options
% 15.93/2.55  
% 15.93/2.55  --schedule                              default
% 15.93/2.55  --add_important_lit                     false
% 15.93/2.55  --prop_solver_per_cl                    1000
% 15.93/2.55  --min_unsat_core                        false
% 15.93/2.55  --soft_assumptions                      false
% 15.93/2.55  --soft_lemma_size                       3
% 15.93/2.55  --prop_impl_unit_size                   0
% 15.93/2.55  --prop_impl_unit                        []
% 15.93/2.55  --share_sel_clauses                     true
% 15.93/2.55  --reset_solvers                         false
% 15.93/2.55  --bc_imp_inh                            [conj_cone]
% 15.93/2.55  --conj_cone_tolerance                   3.
% 15.93/2.55  --extra_neg_conj                        none
% 15.93/2.55  --large_theory_mode                     true
% 15.93/2.55  --prolific_symb_bound                   200
% 15.93/2.55  --lt_threshold                          2000
% 15.93/2.55  --clause_weak_htbl                      true
% 15.93/2.55  --gc_record_bc_elim                     false
% 15.93/2.55  
% 15.93/2.55  ------ Preprocessing Options
% 15.93/2.55  
% 15.93/2.55  --preprocessing_flag                    true
% 15.93/2.55  --time_out_prep_mult                    0.1
% 15.93/2.55  --splitting_mode                        input
% 15.93/2.55  --splitting_grd                         true
% 15.93/2.55  --splitting_cvd                         false
% 15.93/2.55  --splitting_cvd_svl                     false
% 15.93/2.55  --splitting_nvd                         32
% 15.93/2.55  --sub_typing                            true
% 15.93/2.55  --prep_gs_sim                           true
% 15.93/2.55  --prep_unflatten                        true
% 15.93/2.55  --prep_res_sim                          true
% 15.93/2.55  --prep_upred                            true
% 15.93/2.55  --prep_sem_filter                       exhaustive
% 15.93/2.55  --prep_sem_filter_out                   false
% 15.93/2.55  --pred_elim                             true
% 15.93/2.55  --res_sim_input                         true
% 15.93/2.55  --eq_ax_congr_red                       true
% 15.93/2.55  --pure_diseq_elim                       true
% 15.93/2.55  --brand_transform                       false
% 15.93/2.55  --non_eq_to_eq                          false
% 15.93/2.55  --prep_def_merge                        true
% 15.93/2.55  --prep_def_merge_prop_impl              false
% 15.93/2.55  --prep_def_merge_mbd                    true
% 15.93/2.55  --prep_def_merge_tr_red                 false
% 15.93/2.55  --prep_def_merge_tr_cl                  false
% 15.93/2.55  --smt_preprocessing                     true
% 15.93/2.55  --smt_ac_axioms                         fast
% 15.93/2.55  --preprocessed_out                      false
% 15.93/2.55  --preprocessed_stats                    false
% 15.93/2.55  
% 15.93/2.55  ------ Abstraction refinement Options
% 15.93/2.55  
% 15.93/2.55  --abstr_ref                             []
% 15.93/2.55  --abstr_ref_prep                        false
% 15.93/2.55  --abstr_ref_until_sat                   false
% 15.93/2.55  --abstr_ref_sig_restrict                funpre
% 15.93/2.55  --abstr_ref_af_restrict_to_split_sk     false
% 15.93/2.55  --abstr_ref_under                       []
% 15.93/2.55  
% 15.93/2.55  ------ SAT Options
% 15.93/2.55  
% 15.93/2.55  --sat_mode                              false
% 15.93/2.55  --sat_fm_restart_options                ""
% 15.93/2.55  --sat_gr_def                            false
% 15.93/2.55  --sat_epr_types                         true
% 15.93/2.55  --sat_non_cyclic_types                  false
% 15.93/2.55  --sat_finite_models                     false
% 15.93/2.55  --sat_fm_lemmas                         false
% 15.93/2.55  --sat_fm_prep                           false
% 15.93/2.55  --sat_fm_uc_incr                        true
% 15.93/2.55  --sat_out_model                         small
% 15.93/2.55  --sat_out_clauses                       false
% 15.93/2.55  
% 15.93/2.55  ------ QBF Options
% 15.93/2.55  
% 15.93/2.55  --qbf_mode                              false
% 15.93/2.55  --qbf_elim_univ                         false
% 15.93/2.55  --qbf_dom_inst                          none
% 15.93/2.55  --qbf_dom_pre_inst                      false
% 15.93/2.55  --qbf_sk_in                             false
% 15.93/2.55  --qbf_pred_elim                         true
% 15.93/2.55  --qbf_split                             512
% 15.93/2.55  
% 15.93/2.55  ------ BMC1 Options
% 15.93/2.55  
% 15.93/2.55  --bmc1_incremental                      false
% 15.93/2.55  --bmc1_axioms                           reachable_all
% 15.93/2.55  --bmc1_min_bound                        0
% 15.93/2.55  --bmc1_max_bound                        -1
% 15.93/2.55  --bmc1_max_bound_default                -1
% 15.93/2.55  --bmc1_symbol_reachability              true
% 15.93/2.55  --bmc1_property_lemmas                  false
% 15.93/2.55  --bmc1_k_induction                      false
% 15.93/2.55  --bmc1_non_equiv_states                 false
% 15.93/2.55  --bmc1_deadlock                         false
% 15.93/2.55  --bmc1_ucm                              false
% 15.93/2.55  --bmc1_add_unsat_core                   none
% 15.93/2.55  --bmc1_unsat_core_children              false
% 15.93/2.55  --bmc1_unsat_core_extrapolate_axioms    false
% 15.93/2.55  --bmc1_out_stat                         full
% 15.93/2.55  --bmc1_ground_init                      false
% 15.93/2.55  --bmc1_pre_inst_next_state              false
% 15.93/2.55  --bmc1_pre_inst_state                   false
% 15.93/2.55  --bmc1_pre_inst_reach_state             false
% 15.93/2.55  --bmc1_out_unsat_core                   false
% 15.93/2.55  --bmc1_aig_witness_out                  false
% 15.93/2.55  --bmc1_verbose                          false
% 15.93/2.55  --bmc1_dump_clauses_tptp                false
% 15.93/2.55  --bmc1_dump_unsat_core_tptp             false
% 15.93/2.55  --bmc1_dump_file                        -
% 15.93/2.55  --bmc1_ucm_expand_uc_limit              128
% 15.93/2.55  --bmc1_ucm_n_expand_iterations          6
% 15.93/2.55  --bmc1_ucm_extend_mode                  1
% 15.93/2.55  --bmc1_ucm_init_mode                    2
% 15.93/2.55  --bmc1_ucm_cone_mode                    none
% 15.93/2.55  --bmc1_ucm_reduced_relation_type        0
% 15.93/2.55  --bmc1_ucm_relax_model                  4
% 15.93/2.55  --bmc1_ucm_full_tr_after_sat            true
% 15.93/2.55  --bmc1_ucm_expand_neg_assumptions       false
% 15.93/2.55  --bmc1_ucm_layered_model                none
% 15.93/2.55  --bmc1_ucm_max_lemma_size               10
% 15.93/2.55  
% 15.93/2.55  ------ AIG Options
% 15.93/2.55  
% 15.93/2.55  --aig_mode                              false
% 15.93/2.55  
% 15.93/2.55  ------ Instantiation Options
% 15.93/2.55  
% 15.93/2.55  --instantiation_flag                    false
% 15.93/2.55  --inst_sos_flag                         false
% 15.93/2.55  --inst_sos_phase                        true
% 15.93/2.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.93/2.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.93/2.55  --inst_lit_sel_side                     num_symb
% 15.93/2.55  --inst_solver_per_active                1400
% 15.93/2.55  --inst_solver_calls_frac                1.
% 15.93/2.55  --inst_passive_queue_type               priority_queues
% 15.93/2.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.93/2.55  --inst_passive_queues_freq              [25;2]
% 15.93/2.55  --inst_dismatching                      true
% 15.93/2.55  --inst_eager_unprocessed_to_passive     true
% 15.93/2.55  --inst_prop_sim_given                   true
% 15.93/2.55  --inst_prop_sim_new                     false
% 15.93/2.55  --inst_subs_new                         false
% 15.93/2.55  --inst_eq_res_simp                      false
% 15.93/2.55  --inst_subs_given                       false
% 15.93/2.55  --inst_orphan_elimination               true
% 15.93/2.55  --inst_learning_loop_flag               true
% 15.93/2.55  --inst_learning_start                   3000
% 15.93/2.55  --inst_learning_factor                  2
% 15.93/2.55  --inst_start_prop_sim_after_learn       3
% 15.93/2.55  --inst_sel_renew                        solver
% 15.93/2.55  --inst_lit_activity_flag                true
% 15.93/2.55  --inst_restr_to_given                   false
% 15.93/2.55  --inst_activity_threshold               500
% 15.93/2.55  --inst_out_proof                        true
% 15.93/2.55  
% 15.93/2.55  ------ Resolution Options
% 15.93/2.55  
% 15.93/2.55  --resolution_flag                       false
% 15.93/2.55  --res_lit_sel                           adaptive
% 15.93/2.55  --res_lit_sel_side                      none
% 15.93/2.55  --res_ordering                          kbo
% 15.93/2.55  --res_to_prop_solver                    active
% 15.93/2.55  --res_prop_simpl_new                    false
% 15.93/2.55  --res_prop_simpl_given                  true
% 15.93/2.55  --res_passive_queue_type                priority_queues
% 15.93/2.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.93/2.55  --res_passive_queues_freq               [15;5]
% 15.93/2.55  --res_forward_subs                      full
% 15.93/2.55  --res_backward_subs                     full
% 15.93/2.55  --res_forward_subs_resolution           true
% 15.93/2.55  --res_backward_subs_resolution          true
% 15.93/2.55  --res_orphan_elimination                true
% 15.93/2.55  --res_time_limit                        2.
% 15.93/2.55  --res_out_proof                         true
% 15.93/2.55  
% 15.93/2.55  ------ Superposition Options
% 15.93/2.55  
% 15.93/2.55  --superposition_flag                    true
% 15.93/2.55  --sup_passive_queue_type                priority_queues
% 15.93/2.55  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.93/2.55  --sup_passive_queues_freq               [8;1;4]
% 15.93/2.55  --demod_completeness_check              fast
% 15.93/2.55  --demod_use_ground                      true
% 15.93/2.55  --sup_to_prop_solver                    active
% 15.93/2.55  --sup_prop_simpl_new                    false
% 15.93/2.55  --sup_prop_simpl_given                  false
% 15.93/2.55  --sup_fun_splitting                     true
% 15.93/2.55  --sup_smt_interval                      10000
% 15.93/2.55  
% 15.93/2.55  ------ Superposition Simplification Setup
% 15.93/2.55  
% 15.93/2.55  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.93/2.55  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.93/2.55  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.93/2.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.93/2.55  --sup_full_triv                         [TrivRules]
% 15.93/2.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.93/2.55  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.93/2.55  --sup_immed_triv                        [TrivRules]
% 15.93/2.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.93/2.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.93/2.55  --sup_immed_bw_main                     []
% 15.93/2.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.93/2.55  --sup_input_triv                        [Unflattening;TrivRules]
% 15.93/2.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.93/2.55  --sup_input_bw                          [BwDemod;BwSubsumption]
% 15.93/2.55  
% 15.93/2.55  ------ Combination Options
% 15.93/2.55  
% 15.93/2.55  --comb_res_mult                         1
% 15.93/2.55  --comb_sup_mult                         1
% 15.93/2.55  --comb_inst_mult                        1000000
% 15.93/2.55  
% 15.93/2.55  ------ Debug Options
% 15.93/2.55  
% 15.93/2.55  --dbg_backtrace                         false
% 15.93/2.55  --dbg_dump_prop_clauses                 false
% 15.93/2.55  --dbg_dump_prop_clauses_file            -
% 15.93/2.55  --dbg_out_stat                          false
% 15.93/2.55  
% 15.93/2.55  
% 15.93/2.55  
% 15.93/2.55  
% 15.93/2.55  ------ Proving...
% 15.93/2.55  
% 15.93/2.55  
% 15.93/2.55  % SZS status Theorem for theBenchmark.p
% 15.93/2.55  
% 15.93/2.55   Resolution empty clause
% 15.93/2.55  
% 15.93/2.55  % SZS output start CNFRefutation for theBenchmark.p
% 15.93/2.55  
% 15.93/2.55  fof(f2,axiom,(
% 15.93/2.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.93/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.93/2.55  
% 15.93/2.55  fof(f22,plain,(
% 15.93/2.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.93/2.55    inference(cnf_transformation,[],[f2])).
% 15.93/2.55  
% 15.93/2.55  fof(f11,axiom,(
% 15.93/2.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.93/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.93/2.55  
% 15.93/2.55  fof(f31,plain,(
% 15.93/2.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.93/2.55    inference(cnf_transformation,[],[f11])).
% 15.93/2.55  
% 15.93/2.55  fof(f34,plain,(
% 15.93/2.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 15.93/2.55    inference(definition_unfolding,[],[f22,f31,f31])).
% 15.93/2.55  
% 15.93/2.55  fof(f8,axiom,(
% 15.93/2.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 15.93/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.93/2.55  
% 15.93/2.55  fof(f28,plain,(
% 15.93/2.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.93/2.55    inference(cnf_transformation,[],[f8])).
% 15.93/2.55  
% 15.93/2.55  fof(f5,axiom,(
% 15.93/2.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 15.93/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.93/2.55  
% 15.93/2.55  fof(f16,plain,(
% 15.93/2.55    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 15.93/2.55    inference(unused_predicate_definition_removal,[],[f5])).
% 15.93/2.55  
% 15.93/2.55  fof(f17,plain,(
% 15.93/2.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 15.93/2.55    inference(ennf_transformation,[],[f16])).
% 15.93/2.55  
% 15.93/2.55  fof(f25,plain,(
% 15.93/2.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 15.93/2.55    inference(cnf_transformation,[],[f17])).
% 15.93/2.55  
% 15.93/2.55  fof(f7,axiom,(
% 15.93/2.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.93/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.93/2.55  
% 15.93/2.55  fof(f27,plain,(
% 15.93/2.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.93/2.55    inference(cnf_transformation,[],[f7])).
% 15.93/2.55  
% 15.93/2.55  fof(f10,axiom,(
% 15.93/2.55    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 15.93/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.93/2.55  
% 15.93/2.55  fof(f30,plain,(
% 15.93/2.55    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 15.93/2.55    inference(cnf_transformation,[],[f10])).
% 15.93/2.55  
% 15.93/2.55  fof(f6,axiom,(
% 15.93/2.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 15.93/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.93/2.55  
% 15.93/2.55  fof(f26,plain,(
% 15.93/2.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.93/2.55    inference(cnf_transformation,[],[f6])).
% 15.93/2.55  
% 15.93/2.55  fof(f9,axiom,(
% 15.93/2.55    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 15.93/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.93/2.55  
% 15.93/2.55  fof(f29,plain,(
% 15.93/2.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 15.93/2.55    inference(cnf_transformation,[],[f9])).
% 15.93/2.55  
% 15.93/2.55  fof(f1,axiom,(
% 15.93/2.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.93/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.93/2.55  
% 15.93/2.55  fof(f21,plain,(
% 15.93/2.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.93/2.55    inference(cnf_transformation,[],[f1])).
% 15.93/2.55  
% 15.93/2.55  fof(f13,conjecture,(
% 15.93/2.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 15.93/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.93/2.55  
% 15.93/2.55  fof(f14,negated_conjecture,(
% 15.93/2.55    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 15.93/2.55    inference(negated_conjecture,[],[f13])).
% 15.93/2.55  
% 15.93/2.55  fof(f18,plain,(
% 15.93/2.55    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 15.93/2.55    inference(ennf_transformation,[],[f14])).
% 15.93/2.55  
% 15.93/2.55  fof(f19,plain,(
% 15.93/2.55    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 15.93/2.55    introduced(choice_axiom,[])).
% 15.93/2.55  
% 15.93/2.55  fof(f20,plain,(
% 15.93/2.55    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 15.93/2.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 15.93/2.55  
% 15.93/2.55  fof(f33,plain,(
% 15.93/2.55    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 15.93/2.55    inference(cnf_transformation,[],[f20])).
% 15.93/2.55  
% 15.93/2.55  fof(f3,axiom,(
% 15.93/2.55    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 15.93/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.93/2.55  
% 15.93/2.55  fof(f23,plain,(
% 15.93/2.55    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 15.93/2.55    inference(cnf_transformation,[],[f3])).
% 15.93/2.55  
% 15.93/2.55  fof(f36,plain,(
% 15.93/2.55    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 15.93/2.55    inference(definition_unfolding,[],[f33,f31,f23,f23])).
% 15.93/2.55  
% 15.93/2.55  fof(f4,axiom,(
% 15.93/2.55    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 15.93/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.93/2.55  
% 15.93/2.55  fof(f15,plain,(
% 15.93/2.55    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 15.93/2.55    inference(rectify,[],[f4])).
% 15.93/2.55  
% 15.93/2.55  fof(f24,plain,(
% 15.93/2.55    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 15.93/2.55    inference(cnf_transformation,[],[f15])).
% 15.93/2.55  
% 15.93/2.55  cnf(c_1,plain,
% 15.93/2.55      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 15.93/2.55      inference(cnf_transformation,[],[f34]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_6,plain,
% 15.93/2.55      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.93/2.55      inference(cnf_transformation,[],[f28]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_3,plain,
% 15.93/2.55      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 15.93/2.55      inference(cnf_transformation,[],[f25]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_5,plain,
% 15.93/2.55      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 15.93/2.55      inference(cnf_transformation,[],[f27]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_46,plain,
% 15.93/2.55      ( X0 != X1
% 15.93/2.55      | k4_xboole_0(X0,X2) != X3
% 15.93/2.55      | k4_xboole_0(X3,X1) = k1_xboole_0 ),
% 15.93/2.55      inference(resolution_lifted,[status(thm)],[c_3,c_5]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_47,plain,
% 15.93/2.55      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 15.93/2.55      inference(unflattening,[status(thm)],[c_46]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_74,plain,
% 15.93/2.55      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_6,c_47]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_8,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 15.93/2.55      inference(cnf_transformation,[],[f30]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_128,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_74,c_8]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_4,plain,
% 15.93/2.55      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.93/2.55      inference(cnf_transformation,[],[f26]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_135,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_128,c_4]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_311,plain,
% 15.93/2.55      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_135,c_1]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_7,plain,
% 15.93/2.55      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.93/2.55      inference(cnf_transformation,[],[f29]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_108,plain,
% 15.93/2.55      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_7,c_47]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_316,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 15.93/2.55      inference(light_normalisation,[status(thm)],[c_311,c_6,c_108]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_557,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_316,c_7]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_0,plain,
% 15.93/2.55      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 15.93/2.55      inference(cnf_transformation,[],[f21]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_10,negated_conjecture,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 15.93/2.55      inference(cnf_transformation,[],[f36]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_63,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_0,c_10]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_49518,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_557,c_63]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_122,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_74,c_8]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_64,plain,
% 15.93/2.55      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_138,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_122,c_64]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_107,plain,
% 15.93/2.55      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_7,c_74]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_328,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_138,c_107]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_94,plain,
% 15.93/2.55      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_535,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) = X0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_47,c_316]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_753,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_535,c_6]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_796,plain,
% 15.93/2.55      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_753,c_0]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_949,plain,
% 15.93/2.55      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = X0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_94,c_796]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_1038,plain,
% 15.93/2.55      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X2))) = X0 ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_949,c_7]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_5979,plain,
% 15.93/2.55      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X0))) = X0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_8,c_1038]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_18363,plain,
% 15.93/2.55      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_328,c_5979]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_18588,plain,
% 15.93/2.55      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 15.93/2.55      inference(light_normalisation,[status(thm)],[c_18363,c_6]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_334,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_138,c_1]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_98,plain,
% 15.93/2.55      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_74,c_7]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_77,plain,
% 15.93/2.55      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_47,c_6]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_113,plain,
% 15.93/2.55      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_98,c_77]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_339,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 15.93/2.55      inference(light_normalisation,[status(thm)],[c_334,c_6,c_113]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_787,plain,
% 15.93/2.55      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_339,c_753]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_1482,plain,
% 15.93/2.55      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_0,c_787]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_305,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_135,c_107]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_118,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X0)) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_8254,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0))),k4_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_305,c_118]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_1657,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_1482,c_316]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_1680,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 15.93/2.55      inference(light_normalisation,[status(thm)],[c_1657,c_108]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_2,plain,
% 15.93/2.55      ( k2_xboole_0(X0,X0) = X0 ),
% 15.93/2.55      inference(cnf_transformation,[],[f24]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_105,plain,
% 15.93/2.55      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_110,plain,
% 15.93/2.55      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_105,c_7]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_3425,plain,
% 15.93/2.55      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_2,c_110]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_3693,plain,
% 15.93/2.55      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_3425,c_107]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_4505,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_3693,c_339]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_4521,plain,
% 15.93/2.55      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_4505,c_6,c_753,c_1680]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_4534,plain,
% 15.93/2.55      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_7,c_4521]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_4803,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X0)))) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_4534,c_8]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_8405,plain,
% 15.93/2.55      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)))),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_8254,c_6,c_305,c_1680,c_4803]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_99,plain,
% 15.93/2.55      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_47,c_7]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_112,plain,
% 15.93/2.55      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_99,c_7,c_77]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_765,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_1,c_753]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_1100,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_112,c_765]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_1137,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_1100,c_7]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_1138,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_1137,c_4]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_869,plain,
% 15.93/2.55      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_339,c_796]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_4774,plain,
% 15.93/2.55      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_869,c_4534]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_6418,plain,
% 15.93/2.55      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X3))) = k4_xboole_0(X0,X1) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_1138,c_4774]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_8406,plain,
% 15.93/2.55      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_8405,c_6418]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_18589,plain,
% 15.93/2.55      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_18588,c_1482,c_8406]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_127,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X2,X3)),X1) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_19051,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X3,X2)),k4_xboole_0(X1,X2)) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_18589,c_127]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_129,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_47,c_8]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_134,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_129,c_4]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_85,plain,
% 15.93/2.55      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_1,c_47]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_211,plain,
% 15.93/2.55      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_85,c_7]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_420,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k1_xboole_0 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_138,c_211]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_950,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = X1 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_94,c_753]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_1037,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = X1 ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_950,c_7]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_5783,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)),X2) = X2 ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_8,c_1037]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_18057,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_420,c_5783]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_18295,plain,
% 15.93/2.55      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 15.93/2.55      inference(light_normalisation,[status(thm)],[c_18057,c_6]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_124,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_11382,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(k4_xboole_0(X1,X2),X2))) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_420,c_124]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_11717,plain,
% 15.93/2.55      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(k4_xboole_0(X1,X2),X2))) ),
% 15.93/2.55      inference(light_normalisation,[status(thm)],[c_11382,c_6]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_121,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),X2) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_9862,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k2_xboole_0(X2,X4))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X3,k2_xboole_0(X2,X4)))),X2) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_4774,c_121]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_2784,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X2,X1)) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_1680,c_8]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_2791,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_2784,c_1680]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_2792,plain,
% 15.93/2.55      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 15.93/2.55      inference(light_normalisation,[status(thm)],[c_2791,c_6]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_10499,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_2792,c_1680]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_11718,plain,
% 15.93/2.55      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_11717,c_420,c_9862,c_10499]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_123,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X0)) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_47,c_8]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_137,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,X0) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_123,c_64]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_2865,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_138,c_137]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_11719,plain,
% 15.93/2.55      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_11718,c_796,c_2865]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_18296,plain,
% 15.93/2.55      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_18295,c_1482,c_11719]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_18646,plain,
% 15.93/2.55      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_134,c_18296]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_18889,plain,
% 15.93/2.55      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_18646,c_18296]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_33033,plain,
% 15.93/2.55      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(X0,k4_xboole_0(X1,X3)) ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_127,c_18889]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_49519,plain,
% 15.93/2.55      ( k4_xboole_0(k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)),k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_49518,c_19051,c_33033]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_49520,plain,
% 15.93/2.55      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 15.93/2.55      inference(demodulation,[status(thm)],[c_49519,c_4,c_47]) ).
% 15.93/2.55  
% 15.93/2.55  cnf(c_50250,plain,
% 15.93/2.55      ( $false ),
% 15.93/2.55      inference(superposition,[status(thm)],[c_1,c_49520]) ).
% 15.93/2.55  
% 15.93/2.55  
% 15.93/2.55  % SZS output end CNFRefutation for theBenchmark.p
% 15.93/2.55  
% 15.93/2.55  ------                               Statistics
% 15.93/2.55  
% 15.93/2.55  ------ General
% 15.93/2.55  
% 15.93/2.55  abstr_ref_over_cycles:                  0
% 15.93/2.55  abstr_ref_under_cycles:                 0
% 15.93/2.55  gc_basic_clause_elim:                   0
% 15.93/2.55  forced_gc_time:                         0
% 15.93/2.55  parsing_time:                           0.01
% 15.93/2.55  unif_index_cands_time:                  0.
% 15.93/2.55  unif_index_add_time:                    0.
% 15.93/2.55  orderings_time:                         0.
% 15.93/2.55  out_proof_time:                         0.01
% 15.93/2.55  total_time:                             1.962
% 15.93/2.55  num_of_symbols:                         39
% 15.93/2.55  num_of_terms:                           81061
% 15.93/2.55  
% 15.93/2.55  ------ Preprocessing
% 15.93/2.55  
% 15.93/2.55  num_of_splits:                          0
% 15.93/2.55  num_of_split_atoms:                     2
% 15.93/2.55  num_of_reused_defs:                     5
% 15.93/2.55  num_eq_ax_congr_red:                    1
% 15.93/2.55  num_of_sem_filtered_clauses:            0
% 15.93/2.55  num_of_subtypes:                        0
% 15.93/2.55  monotx_restored_types:                  0
% 15.93/2.55  sat_num_of_epr_types:                   0
% 15.93/2.55  sat_num_of_non_cyclic_types:            0
% 15.93/2.55  sat_guarded_non_collapsed_types:        0
% 15.93/2.55  num_pure_diseq_elim:                    0
% 15.93/2.55  simp_replaced_by:                       0
% 15.93/2.55  res_preprocessed:                       35
% 15.93/2.55  prep_upred:                             0
% 15.93/2.55  prep_unflattend:                        2
% 15.93/2.55  smt_new_axioms:                         0
% 15.93/2.55  pred_elim_cands:                        0
% 15.93/2.55  pred_elim:                              1
% 15.93/2.55  pred_elim_cl:                           1
% 15.93/2.55  pred_elim_cycles:                       2
% 15.93/2.55  merged_defs:                            0
% 15.93/2.55  merged_defs_ncl:                        0
% 15.93/2.55  bin_hyper_res:                          0
% 15.93/2.55  prep_cycles:                            3
% 15.93/2.55  pred_elim_time:                         0.
% 15.93/2.55  splitting_time:                         0.
% 15.93/2.55  sem_filter_time:                        0.
% 15.93/2.55  monotx_time:                            0.
% 15.93/2.55  subtype_inf_time:                       0.
% 15.93/2.55  
% 15.93/2.55  ------ Problem properties
% 15.93/2.55  
% 15.93/2.55  clauses:                                10
% 15.93/2.55  conjectures:                            1
% 15.93/2.55  epr:                                    0
% 15.93/2.55  horn:                                   10
% 15.93/2.55  ground:                                 1
% 15.93/2.55  unary:                                  10
% 15.93/2.55  binary:                                 0
% 15.93/2.55  lits:                                   10
% 15.93/2.55  lits_eq:                                10
% 15.93/2.55  fd_pure:                                0
% 15.93/2.55  fd_pseudo:                              0
% 15.93/2.55  fd_cond:                                0
% 15.93/2.55  fd_pseudo_cond:                         0
% 15.93/2.55  ac_symbols:                             1
% 15.93/2.55  
% 15.93/2.55  ------ Propositional Solver
% 15.93/2.55  
% 15.93/2.55  prop_solver_calls:                      17
% 15.93/2.55  prop_fast_solver_calls:                 85
% 15.93/2.55  smt_solver_calls:                       0
% 15.93/2.55  smt_fast_solver_calls:                  0
% 15.93/2.55  prop_num_of_clauses:                    338
% 15.93/2.55  prop_preprocess_simplified:             564
% 15.93/2.55  prop_fo_subsumed:                       0
% 15.93/2.55  prop_solver_time:                       0.
% 15.93/2.55  smt_solver_time:                        0.
% 15.93/2.55  smt_fast_solver_time:                   0.
% 15.93/2.55  prop_fast_solver_time:                  0.
% 15.93/2.55  prop_unsat_core_time:                   0.
% 15.93/2.55  
% 15.93/2.55  ------ QBF
% 15.93/2.55  
% 15.93/2.55  qbf_q_res:                              0
% 15.93/2.55  qbf_num_tautologies:                    0
% 15.93/2.55  qbf_prep_cycles:                        0
% 15.93/2.55  
% 15.93/2.55  ------ BMC1
% 15.93/2.55  
% 15.93/2.55  bmc1_current_bound:                     -1
% 15.93/2.55  bmc1_last_solved_bound:                 -1
% 15.93/2.55  bmc1_unsat_core_size:                   -1
% 15.93/2.55  bmc1_unsat_core_parents_size:           -1
% 15.93/2.55  bmc1_merge_next_fun:                    0
% 15.93/2.55  bmc1_unsat_core_clauses_time:           0.
% 15.93/2.55  
% 15.93/2.55  ------ Instantiation
% 15.93/2.55  
% 15.93/2.55  inst_num_of_clauses:                    0
% 15.93/2.55  inst_num_in_passive:                    0
% 15.93/2.55  inst_num_in_active:                     0
% 15.93/2.55  inst_num_in_unprocessed:                0
% 15.93/2.55  inst_num_of_loops:                      0
% 15.93/2.55  inst_num_of_learning_restarts:          0
% 15.93/2.55  inst_num_moves_active_passive:          0
% 15.93/2.55  inst_lit_activity:                      0
% 15.93/2.55  inst_lit_activity_moves:                0
% 15.93/2.55  inst_num_tautologies:                   0
% 15.93/2.55  inst_num_prop_implied:                  0
% 15.93/2.55  inst_num_existing_simplified:           0
% 15.93/2.55  inst_num_eq_res_simplified:             0
% 15.93/2.55  inst_num_child_elim:                    0
% 15.93/2.55  inst_num_of_dismatching_blockings:      0
% 15.93/2.55  inst_num_of_non_proper_insts:           0
% 15.93/2.55  inst_num_of_duplicates:                 0
% 15.93/2.55  inst_inst_num_from_inst_to_res:         0
% 15.93/2.55  inst_dismatching_checking_time:         0.
% 15.93/2.55  
% 15.93/2.55  ------ Resolution
% 15.93/2.55  
% 15.93/2.55  res_num_of_clauses:                     0
% 15.93/2.55  res_num_in_passive:                     0
% 15.93/2.55  res_num_in_active:                      0
% 15.93/2.55  res_num_of_loops:                       38
% 15.93/2.55  res_forward_subset_subsumed:            0
% 15.93/2.55  res_backward_subset_subsumed:           0
% 15.93/2.55  res_forward_subsumed:                   0
% 15.93/2.55  res_backward_subsumed:                  0
% 15.93/2.55  res_forward_subsumption_resolution:     0
% 15.93/2.55  res_backward_subsumption_resolution:    0
% 15.93/2.55  res_clause_to_clause_subsumption:       137173
% 15.93/2.55  res_orphan_elimination:                 0
% 15.93/2.55  res_tautology_del:                      0
% 15.93/2.55  res_num_eq_res_simplified:              0
% 15.93/2.55  res_num_sel_changes:                    0
% 15.93/2.55  res_moves_from_active_to_pass:          0
% 15.93/2.55  
% 15.93/2.55  ------ Superposition
% 15.93/2.55  
% 15.93/2.55  sup_time_total:                         0.
% 15.93/2.55  sup_time_generating:                    0.
% 15.93/2.55  sup_time_sim_full:                      0.
% 15.93/2.55  sup_time_sim_immed:                     0.
% 15.93/2.55  
% 15.93/2.55  sup_num_of_clauses:                     5604
% 15.93/2.55  sup_num_in_active:                      156
% 15.93/2.55  sup_num_in_passive:                     5448
% 15.93/2.55  sup_num_of_loops:                       195
% 15.93/2.55  sup_fw_superposition:                   18707
% 15.93/2.55  sup_bw_superposition:                   15831
% 15.93/2.55  sup_immediate_simplified:               14740
% 15.93/2.55  sup_given_eliminated:                   9
% 15.93/2.55  comparisons_done:                       0
% 15.93/2.55  comparisons_avoided:                    0
% 15.93/2.55  
% 15.93/2.55  ------ Simplifications
% 15.93/2.55  
% 15.93/2.55  
% 15.93/2.55  sim_fw_subset_subsumed:                 0
% 15.93/2.55  sim_bw_subset_subsumed:                 0
% 15.93/2.55  sim_fw_subsumed:                        2221
% 15.93/2.55  sim_bw_subsumed:                        83
% 15.93/2.55  sim_fw_subsumption_res:                 0
% 15.93/2.55  sim_bw_subsumption_res:                 0
% 15.93/2.55  sim_tautology_del:                      0
% 15.93/2.55  sim_eq_tautology_del:                   4388
% 15.93/2.55  sim_eq_res_simp:                        0
% 15.93/2.55  sim_fw_demodulated:                     10017
% 15.93/2.55  sim_bw_demodulated:                     211
% 15.93/2.55  sim_light_normalised:                   5216
% 15.93/2.55  sim_joinable_taut:                      76
% 15.93/2.55  sim_joinable_simp:                      0
% 15.93/2.55  sim_ac_normalised:                      0
% 15.93/2.55  sim_smt_subsumption:                    0
% 15.93/2.55  
%------------------------------------------------------------------------------
