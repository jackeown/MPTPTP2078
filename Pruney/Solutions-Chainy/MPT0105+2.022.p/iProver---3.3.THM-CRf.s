%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:15 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  120 (1656 expanded)
%              Number of clauses        :   74 ( 629 expanded)
%              Number of leaves         :   17 ( 444 expanded)
%              Depth                    :   25
%              Number of atoms          :  128 (1664 expanded)
%              Number of equality atoms :  119 (1655 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f34])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f25,f42,f42])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f13,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) ),
    inference(definition_unfolding,[],[f39,f42,f42,f42,f42])).

fof(f16,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(definition_unfolding,[],[f40,f42,f42,f34])).

fof(f17,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f17])).

fof(f22,plain,(
    ? [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f18])).

fof(f23,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_xboole_0(X0,X1)
   => k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f41,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    k2_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f41,f42])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_79,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_7])).

cnf(c_116,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_79])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_117,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_116,c_3])).

cnf(c_257,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_117,c_3])).

cnf(c_82,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_79,c_3])).

cnf(c_84,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_82,c_2])).

cnf(c_259,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_257,c_84])).

cnf(c_1,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_640,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1))) = k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_259,c_1])).

cnf(c_5,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_129,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_5,c_8])).

cnf(c_150,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_129,c_5])).

cnf(c_642,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0)))) = k4_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_640,c_5,c_150])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_90,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_3])).

cnf(c_93,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_90,c_3])).

cnf(c_643,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_642,c_4,c_93,c_117])).

cnf(c_9,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_345,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_9,c_93])).

cnf(c_154,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_357,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_345,c_154])).

cnf(c_249,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_117])).

cnf(c_285,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_249,c_6])).

cnf(c_11,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_54,plain,
    ( X0 != X1
    | k4_xboole_0(X2,X1) != X3
    | k4_xboole_0(X3,X0) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_12])).

cnf(c_55,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(unflattening,[status(thm)],[c_54])).

cnf(c_96,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_79,c_55])).

cnf(c_97,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_96,c_79])).

cnf(c_298,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_285,c_6,c_97])).

cnf(c_738,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_298,c_6])).

cnf(c_1344,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_357,c_738])).

cnf(c_1665,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1344,c_6])).

cnf(c_1702,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_93,c_1665])).

cnf(c_13,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_77,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2)))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) ),
    inference(demodulation,[status(thm)],[c_13,c_6])).

cnf(c_78,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) ),
    inference(demodulation,[status(thm)],[c_77,c_6])).

cnf(c_5239,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X0))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X0))))))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k2_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_1702,c_78])).

cnf(c_558,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_357])).

cnf(c_5242,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X0))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X0))))))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0))) ),
    inference(light_normalisation,[status(thm)],[c_5239,c_558])).

cnf(c_288,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_249,c_3])).

cnf(c_292,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_288,c_84])).

cnf(c_888,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_643,c_3])).

cnf(c_890,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_888,c_3])).

cnf(c_89,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_2320,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_1,c_89])).

cnf(c_0,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_74,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_0,c_6])).

cnf(c_75,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_74,c_3])).

cnf(c_76,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X1)))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_75,c_3])).

cnf(c_358,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_76,c_4,c_117])).

cnf(c_866,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_358,c_643])).

cnf(c_978,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))))))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_117,c_78])).

cnf(c_1323,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_978,c_4,c_8,c_84,c_93,c_117,c_292,c_357,c_643])).

cnf(c_1381,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_358,c_890])).

cnf(c_1395,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_890,c_358])).

cnf(c_1417,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1395,c_890])).

cnf(c_1418,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1417,c_4,c_7,c_643])).

cnf(c_1424,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1381,c_1418])).

cnf(c_1425,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1424,c_357])).

cnf(c_2423,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_2320,c_866,c_1323,c_1425])).

cnf(c_5243,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_5242,c_4,c_7,c_8,c_84,c_292,c_643,c_890,c_2423])).

cnf(c_7649,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_643,c_5243])).

cnf(c_7818,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7649,c_4,c_7,c_89])).

cnf(c_14,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_73,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_14,c_3])).

cnf(c_8068,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_7818,c_73])).

cnf(c_8070,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_8068,c_4,c_79])).

cnf(c_8071,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8070])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.80/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.02  
% 3.80/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.80/1.02  
% 3.80/1.02  ------  iProver source info
% 3.80/1.02  
% 3.80/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.80/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.80/1.02  git: non_committed_changes: false
% 3.80/1.02  git: last_make_outside_of_git: false
% 3.80/1.02  
% 3.80/1.02  ------ 
% 3.80/1.02  
% 3.80/1.02  ------ Input Options
% 3.80/1.02  
% 3.80/1.02  --out_options                           all
% 3.80/1.02  --tptp_safe_out                         true
% 3.80/1.02  --problem_path                          ""
% 3.80/1.02  --include_path                          ""
% 3.80/1.02  --clausifier                            res/vclausify_rel
% 3.80/1.02  --clausifier_options                    --mode clausify
% 3.80/1.02  --stdin                                 false
% 3.80/1.02  --stats_out                             all
% 3.80/1.02  
% 3.80/1.02  ------ General Options
% 3.80/1.02  
% 3.80/1.02  --fof                                   false
% 3.80/1.02  --time_out_real                         305.
% 3.80/1.02  --time_out_virtual                      -1.
% 3.80/1.02  --symbol_type_check                     false
% 3.80/1.02  --clausify_out                          false
% 3.80/1.02  --sig_cnt_out                           false
% 3.80/1.02  --trig_cnt_out                          false
% 3.80/1.02  --trig_cnt_out_tolerance                1.
% 3.80/1.02  --trig_cnt_out_sk_spl                   false
% 3.80/1.02  --abstr_cl_out                          false
% 3.80/1.02  
% 3.80/1.02  ------ Global Options
% 3.80/1.02  
% 3.80/1.02  --schedule                              default
% 3.80/1.02  --add_important_lit                     false
% 3.80/1.02  --prop_solver_per_cl                    1000
% 3.80/1.02  --min_unsat_core                        false
% 3.80/1.02  --soft_assumptions                      false
% 3.80/1.02  --soft_lemma_size                       3
% 3.80/1.02  --prop_impl_unit_size                   0
% 3.80/1.02  --prop_impl_unit                        []
% 3.80/1.02  --share_sel_clauses                     true
% 3.80/1.02  --reset_solvers                         false
% 3.80/1.02  --bc_imp_inh                            [conj_cone]
% 3.80/1.02  --conj_cone_tolerance                   3.
% 3.80/1.02  --extra_neg_conj                        none
% 3.80/1.02  --large_theory_mode                     true
% 3.80/1.02  --prolific_symb_bound                   200
% 3.80/1.02  --lt_threshold                          2000
% 3.80/1.02  --clause_weak_htbl                      true
% 3.80/1.02  --gc_record_bc_elim                     false
% 3.80/1.02  
% 3.80/1.02  ------ Preprocessing Options
% 3.80/1.02  
% 3.80/1.02  --preprocessing_flag                    true
% 3.80/1.02  --time_out_prep_mult                    0.1
% 3.80/1.02  --splitting_mode                        input
% 3.80/1.02  --splitting_grd                         true
% 3.80/1.02  --splitting_cvd                         false
% 3.80/1.02  --splitting_cvd_svl                     false
% 3.80/1.02  --splitting_nvd                         32
% 3.80/1.02  --sub_typing                            true
% 3.80/1.02  --prep_gs_sim                           true
% 3.80/1.02  --prep_unflatten                        true
% 3.80/1.02  --prep_res_sim                          true
% 3.80/1.02  --prep_upred                            true
% 3.80/1.02  --prep_sem_filter                       exhaustive
% 3.80/1.02  --prep_sem_filter_out                   false
% 3.80/1.02  --pred_elim                             true
% 3.80/1.02  --res_sim_input                         true
% 3.80/1.02  --eq_ax_congr_red                       true
% 3.80/1.02  --pure_diseq_elim                       true
% 3.80/1.02  --brand_transform                       false
% 3.80/1.02  --non_eq_to_eq                          false
% 3.80/1.02  --prep_def_merge                        true
% 3.80/1.02  --prep_def_merge_prop_impl              false
% 3.80/1.02  --prep_def_merge_mbd                    true
% 3.80/1.02  --prep_def_merge_tr_red                 false
% 3.80/1.02  --prep_def_merge_tr_cl                  false
% 3.80/1.02  --smt_preprocessing                     true
% 3.80/1.02  --smt_ac_axioms                         fast
% 3.80/1.02  --preprocessed_out                      false
% 3.80/1.02  --preprocessed_stats                    false
% 3.80/1.02  
% 3.80/1.02  ------ Abstraction refinement Options
% 3.80/1.02  
% 3.80/1.02  --abstr_ref                             []
% 3.80/1.02  --abstr_ref_prep                        false
% 3.80/1.02  --abstr_ref_until_sat                   false
% 3.80/1.02  --abstr_ref_sig_restrict                funpre
% 3.80/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.80/1.02  --abstr_ref_under                       []
% 3.80/1.02  
% 3.80/1.02  ------ SAT Options
% 3.80/1.02  
% 3.80/1.02  --sat_mode                              false
% 3.80/1.02  --sat_fm_restart_options                ""
% 3.80/1.02  --sat_gr_def                            false
% 3.80/1.02  --sat_epr_types                         true
% 3.80/1.02  --sat_non_cyclic_types                  false
% 3.80/1.02  --sat_finite_models                     false
% 3.80/1.02  --sat_fm_lemmas                         false
% 3.80/1.02  --sat_fm_prep                           false
% 3.80/1.02  --sat_fm_uc_incr                        true
% 3.80/1.02  --sat_out_model                         small
% 3.80/1.02  --sat_out_clauses                       false
% 3.80/1.02  
% 3.80/1.02  ------ QBF Options
% 3.80/1.02  
% 3.80/1.02  --qbf_mode                              false
% 3.80/1.02  --qbf_elim_univ                         false
% 3.80/1.02  --qbf_dom_inst                          none
% 3.80/1.02  --qbf_dom_pre_inst                      false
% 3.80/1.02  --qbf_sk_in                             false
% 3.80/1.02  --qbf_pred_elim                         true
% 3.80/1.02  --qbf_split                             512
% 3.80/1.02  
% 3.80/1.02  ------ BMC1 Options
% 3.80/1.02  
% 3.80/1.02  --bmc1_incremental                      false
% 3.80/1.02  --bmc1_axioms                           reachable_all
% 3.80/1.02  --bmc1_min_bound                        0
% 3.80/1.02  --bmc1_max_bound                        -1
% 3.80/1.02  --bmc1_max_bound_default                -1
% 3.80/1.02  --bmc1_symbol_reachability              true
% 3.80/1.02  --bmc1_property_lemmas                  false
% 3.80/1.02  --bmc1_k_induction                      false
% 3.80/1.02  --bmc1_non_equiv_states                 false
% 3.80/1.02  --bmc1_deadlock                         false
% 3.80/1.02  --bmc1_ucm                              false
% 3.80/1.02  --bmc1_add_unsat_core                   none
% 3.80/1.02  --bmc1_unsat_core_children              false
% 3.80/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.80/1.02  --bmc1_out_stat                         full
% 3.80/1.02  --bmc1_ground_init                      false
% 3.80/1.02  --bmc1_pre_inst_next_state              false
% 3.80/1.02  --bmc1_pre_inst_state                   false
% 3.80/1.02  --bmc1_pre_inst_reach_state             false
% 3.80/1.02  --bmc1_out_unsat_core                   false
% 3.80/1.02  --bmc1_aig_witness_out                  false
% 3.80/1.02  --bmc1_verbose                          false
% 3.80/1.02  --bmc1_dump_clauses_tptp                false
% 3.80/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.80/1.02  --bmc1_dump_file                        -
% 3.80/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.80/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.80/1.02  --bmc1_ucm_extend_mode                  1
% 3.80/1.02  --bmc1_ucm_init_mode                    2
% 3.80/1.02  --bmc1_ucm_cone_mode                    none
% 3.80/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.80/1.02  --bmc1_ucm_relax_model                  4
% 3.80/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.80/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.80/1.02  --bmc1_ucm_layered_model                none
% 3.80/1.02  --bmc1_ucm_max_lemma_size               10
% 3.80/1.02  
% 3.80/1.02  ------ AIG Options
% 3.80/1.02  
% 3.80/1.02  --aig_mode                              false
% 3.80/1.02  
% 3.80/1.02  ------ Instantiation Options
% 3.80/1.02  
% 3.80/1.02  --instantiation_flag                    true
% 3.80/1.02  --inst_sos_flag                         false
% 3.80/1.02  --inst_sos_phase                        true
% 3.80/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.80/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.80/1.02  --inst_lit_sel_side                     num_symb
% 3.80/1.02  --inst_solver_per_active                1400
% 3.80/1.02  --inst_solver_calls_frac                1.
% 3.80/1.02  --inst_passive_queue_type               priority_queues
% 3.80/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.80/1.02  --inst_passive_queues_freq              [25;2]
% 3.80/1.02  --inst_dismatching                      true
% 3.80/1.02  --inst_eager_unprocessed_to_passive     true
% 3.80/1.02  --inst_prop_sim_given                   true
% 3.80/1.02  --inst_prop_sim_new                     false
% 3.80/1.02  --inst_subs_new                         false
% 3.80/1.02  --inst_eq_res_simp                      false
% 3.80/1.02  --inst_subs_given                       false
% 3.80/1.02  --inst_orphan_elimination               true
% 3.80/1.02  --inst_learning_loop_flag               true
% 3.80/1.02  --inst_learning_start                   3000
% 3.80/1.02  --inst_learning_factor                  2
% 3.80/1.02  --inst_start_prop_sim_after_learn       3
% 3.80/1.02  --inst_sel_renew                        solver
% 3.80/1.02  --inst_lit_activity_flag                true
% 3.80/1.02  --inst_restr_to_given                   false
% 3.80/1.02  --inst_activity_threshold               500
% 3.80/1.02  --inst_out_proof                        true
% 3.80/1.02  
% 3.80/1.02  ------ Resolution Options
% 3.80/1.02  
% 3.80/1.02  --resolution_flag                       true
% 3.80/1.02  --res_lit_sel                           adaptive
% 3.80/1.02  --res_lit_sel_side                      none
% 3.80/1.02  --res_ordering                          kbo
% 3.80/1.02  --res_to_prop_solver                    active
% 3.80/1.02  --res_prop_simpl_new                    false
% 3.80/1.02  --res_prop_simpl_given                  true
% 3.80/1.02  --res_passive_queue_type                priority_queues
% 3.80/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.80/1.02  --res_passive_queues_freq               [15;5]
% 3.80/1.02  --res_forward_subs                      full
% 3.80/1.02  --res_backward_subs                     full
% 3.80/1.02  --res_forward_subs_resolution           true
% 3.80/1.02  --res_backward_subs_resolution          true
% 3.80/1.02  --res_orphan_elimination                true
% 3.80/1.02  --res_time_limit                        2.
% 3.80/1.02  --res_out_proof                         true
% 3.80/1.02  
% 3.80/1.02  ------ Superposition Options
% 3.80/1.02  
% 3.80/1.02  --superposition_flag                    true
% 3.80/1.02  --sup_passive_queue_type                priority_queues
% 3.80/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.80/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.80/1.02  --demod_completeness_check              fast
% 3.80/1.02  --demod_use_ground                      true
% 3.80/1.02  --sup_to_prop_solver                    passive
% 3.80/1.02  --sup_prop_simpl_new                    true
% 3.80/1.02  --sup_prop_simpl_given                  true
% 3.80/1.02  --sup_fun_splitting                     false
% 3.80/1.02  --sup_smt_interval                      50000
% 3.80/1.02  
% 3.80/1.02  ------ Superposition Simplification Setup
% 3.80/1.02  
% 3.80/1.02  --sup_indices_passive                   []
% 3.80/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.80/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.80/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.80/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.80/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.80/1.02  --sup_full_bw                           [BwDemod]
% 3.80/1.02  --sup_immed_triv                        [TrivRules]
% 3.80/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.80/1.02  --sup_immed_bw_main                     []
% 3.80/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.80/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.80/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.80/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.80/1.02  
% 3.80/1.02  ------ Combination Options
% 3.80/1.02  
% 3.80/1.02  --comb_res_mult                         3
% 3.80/1.02  --comb_sup_mult                         2
% 3.80/1.02  --comb_inst_mult                        10
% 3.80/1.02  
% 3.80/1.02  ------ Debug Options
% 3.80/1.02  
% 3.80/1.02  --dbg_backtrace                         false
% 3.80/1.02  --dbg_dump_prop_clauses                 false
% 3.80/1.02  --dbg_dump_prop_clauses_file            -
% 3.80/1.02  --dbg_out_stat                          false
% 3.80/1.02  ------ Parsing...
% 3.80/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.80/1.02  
% 3.80/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.80/1.02  
% 3.80/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.80/1.02  
% 3.80/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.80/1.02  ------ Proving...
% 3.80/1.02  ------ Problem Properties 
% 3.80/1.02  
% 3.80/1.02  
% 3.80/1.02  clauses                                 14
% 3.80/1.02  conjectures                             1
% 3.80/1.02  EPR                                     0
% 3.80/1.02  Horn                                    14
% 3.80/1.02  unary                                   14
% 3.80/1.02  binary                                  0
% 3.80/1.02  lits                                    14
% 3.80/1.02  lits eq                                 14
% 3.80/1.02  fd_pure                                 0
% 3.80/1.02  fd_pseudo                               0
% 3.80/1.02  fd_cond                                 0
% 3.80/1.02  fd_pseudo_cond                          0
% 3.80/1.02  AC symbols                              0
% 3.80/1.02  
% 3.80/1.02  ------ Schedule UEQ
% 3.80/1.02  
% 3.80/1.02  ------ pure equality problem: resolution off 
% 3.80/1.02  
% 3.80/1.02  ------ Option_UEQ Time Limit: Unbounded
% 3.80/1.02  
% 3.80/1.02  
% 3.80/1.02  ------ 
% 3.80/1.02  Current options:
% 3.80/1.02  ------ 
% 3.80/1.02  
% 3.80/1.02  ------ Input Options
% 3.80/1.02  
% 3.80/1.02  --out_options                           all
% 3.80/1.02  --tptp_safe_out                         true
% 3.80/1.02  --problem_path                          ""
% 3.80/1.02  --include_path                          ""
% 3.80/1.02  --clausifier                            res/vclausify_rel
% 3.80/1.02  --clausifier_options                    --mode clausify
% 3.80/1.02  --stdin                                 false
% 3.80/1.02  --stats_out                             all
% 3.80/1.02  
% 3.80/1.02  ------ General Options
% 3.80/1.02  
% 3.80/1.02  --fof                                   false
% 3.80/1.02  --time_out_real                         305.
% 3.80/1.02  --time_out_virtual                      -1.
% 3.80/1.02  --symbol_type_check                     false
% 3.80/1.02  --clausify_out                          false
% 3.80/1.02  --sig_cnt_out                           false
% 3.80/1.02  --trig_cnt_out                          false
% 3.80/1.02  --trig_cnt_out_tolerance                1.
% 3.80/1.02  --trig_cnt_out_sk_spl                   false
% 3.80/1.02  --abstr_cl_out                          false
% 3.80/1.02  
% 3.80/1.02  ------ Global Options
% 3.80/1.02  
% 3.80/1.02  --schedule                              default
% 3.80/1.02  --add_important_lit                     false
% 3.80/1.02  --prop_solver_per_cl                    1000
% 3.80/1.02  --min_unsat_core                        false
% 3.80/1.02  --soft_assumptions                      false
% 3.80/1.02  --soft_lemma_size                       3
% 3.80/1.02  --prop_impl_unit_size                   0
% 3.80/1.02  --prop_impl_unit                        []
% 3.80/1.02  --share_sel_clauses                     true
% 3.80/1.02  --reset_solvers                         false
% 3.80/1.02  --bc_imp_inh                            [conj_cone]
% 3.80/1.02  --conj_cone_tolerance                   3.
% 3.80/1.02  --extra_neg_conj                        none
% 3.80/1.02  --large_theory_mode                     true
% 3.80/1.02  --prolific_symb_bound                   200
% 3.80/1.02  --lt_threshold                          2000
% 3.80/1.02  --clause_weak_htbl                      true
% 3.80/1.02  --gc_record_bc_elim                     false
% 3.80/1.02  
% 3.80/1.02  ------ Preprocessing Options
% 3.80/1.02  
% 3.80/1.02  --preprocessing_flag                    true
% 3.80/1.02  --time_out_prep_mult                    0.1
% 3.80/1.02  --splitting_mode                        input
% 3.80/1.02  --splitting_grd                         true
% 3.80/1.02  --splitting_cvd                         false
% 3.80/1.02  --splitting_cvd_svl                     false
% 3.80/1.02  --splitting_nvd                         32
% 3.80/1.02  --sub_typing                            true
% 3.80/1.02  --prep_gs_sim                           true
% 3.80/1.02  --prep_unflatten                        true
% 3.80/1.02  --prep_res_sim                          true
% 3.80/1.02  --prep_upred                            true
% 3.80/1.02  --prep_sem_filter                       exhaustive
% 3.80/1.02  --prep_sem_filter_out                   false
% 3.80/1.02  --pred_elim                             true
% 3.80/1.02  --res_sim_input                         true
% 3.80/1.02  --eq_ax_congr_red                       true
% 3.80/1.02  --pure_diseq_elim                       true
% 3.80/1.02  --brand_transform                       false
% 3.80/1.02  --non_eq_to_eq                          false
% 3.80/1.02  --prep_def_merge                        true
% 3.80/1.02  --prep_def_merge_prop_impl              false
% 3.80/1.02  --prep_def_merge_mbd                    true
% 3.80/1.02  --prep_def_merge_tr_red                 false
% 3.80/1.02  --prep_def_merge_tr_cl                  false
% 3.80/1.02  --smt_preprocessing                     true
% 3.80/1.02  --smt_ac_axioms                         fast
% 3.80/1.02  --preprocessed_out                      false
% 3.80/1.02  --preprocessed_stats                    false
% 3.80/1.02  
% 3.80/1.02  ------ Abstraction refinement Options
% 3.80/1.02  
% 3.80/1.02  --abstr_ref                             []
% 3.80/1.02  --abstr_ref_prep                        false
% 3.80/1.02  --abstr_ref_until_sat                   false
% 3.80/1.02  --abstr_ref_sig_restrict                funpre
% 3.80/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.80/1.02  --abstr_ref_under                       []
% 3.80/1.02  
% 3.80/1.02  ------ SAT Options
% 3.80/1.02  
% 3.80/1.02  --sat_mode                              false
% 3.80/1.02  --sat_fm_restart_options                ""
% 3.80/1.02  --sat_gr_def                            false
% 3.80/1.02  --sat_epr_types                         true
% 3.80/1.02  --sat_non_cyclic_types                  false
% 3.80/1.02  --sat_finite_models                     false
% 3.80/1.02  --sat_fm_lemmas                         false
% 3.80/1.02  --sat_fm_prep                           false
% 3.80/1.02  --sat_fm_uc_incr                        true
% 3.80/1.02  --sat_out_model                         small
% 3.80/1.02  --sat_out_clauses                       false
% 3.80/1.02  
% 3.80/1.02  ------ QBF Options
% 3.80/1.02  
% 3.80/1.02  --qbf_mode                              false
% 3.80/1.02  --qbf_elim_univ                         false
% 3.80/1.02  --qbf_dom_inst                          none
% 3.80/1.02  --qbf_dom_pre_inst                      false
% 3.80/1.02  --qbf_sk_in                             false
% 3.80/1.02  --qbf_pred_elim                         true
% 3.80/1.02  --qbf_split                             512
% 3.80/1.02  
% 3.80/1.02  ------ BMC1 Options
% 3.80/1.02  
% 3.80/1.02  --bmc1_incremental                      false
% 3.80/1.02  --bmc1_axioms                           reachable_all
% 3.80/1.02  --bmc1_min_bound                        0
% 3.80/1.02  --bmc1_max_bound                        -1
% 3.80/1.02  --bmc1_max_bound_default                -1
% 3.80/1.02  --bmc1_symbol_reachability              true
% 3.80/1.02  --bmc1_property_lemmas                  false
% 3.80/1.02  --bmc1_k_induction                      false
% 3.80/1.02  --bmc1_non_equiv_states                 false
% 3.80/1.02  --bmc1_deadlock                         false
% 3.80/1.02  --bmc1_ucm                              false
% 3.80/1.02  --bmc1_add_unsat_core                   none
% 3.80/1.02  --bmc1_unsat_core_children              false
% 3.80/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.80/1.02  --bmc1_out_stat                         full
% 3.80/1.02  --bmc1_ground_init                      false
% 3.80/1.02  --bmc1_pre_inst_next_state              false
% 3.80/1.02  --bmc1_pre_inst_state                   false
% 3.80/1.02  --bmc1_pre_inst_reach_state             false
% 3.80/1.02  --bmc1_out_unsat_core                   false
% 3.80/1.02  --bmc1_aig_witness_out                  false
% 3.80/1.02  --bmc1_verbose                          false
% 3.80/1.02  --bmc1_dump_clauses_tptp                false
% 3.80/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.80/1.02  --bmc1_dump_file                        -
% 3.80/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.80/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.80/1.02  --bmc1_ucm_extend_mode                  1
% 3.80/1.02  --bmc1_ucm_init_mode                    2
% 3.80/1.02  --bmc1_ucm_cone_mode                    none
% 3.80/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.80/1.02  --bmc1_ucm_relax_model                  4
% 3.80/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.80/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.80/1.02  --bmc1_ucm_layered_model                none
% 3.80/1.02  --bmc1_ucm_max_lemma_size               10
% 3.80/1.02  
% 3.80/1.02  ------ AIG Options
% 3.80/1.02  
% 3.80/1.02  --aig_mode                              false
% 3.80/1.02  
% 3.80/1.02  ------ Instantiation Options
% 3.80/1.02  
% 3.80/1.02  --instantiation_flag                    false
% 3.80/1.02  --inst_sos_flag                         false
% 3.80/1.02  --inst_sos_phase                        true
% 3.80/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.80/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.80/1.02  --inst_lit_sel_side                     num_symb
% 3.80/1.02  --inst_solver_per_active                1400
% 3.80/1.02  --inst_solver_calls_frac                1.
% 3.80/1.02  --inst_passive_queue_type               priority_queues
% 3.80/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.80/1.02  --inst_passive_queues_freq              [25;2]
% 3.80/1.02  --inst_dismatching                      true
% 3.80/1.02  --inst_eager_unprocessed_to_passive     true
% 3.80/1.02  --inst_prop_sim_given                   true
% 3.80/1.02  --inst_prop_sim_new                     false
% 3.80/1.02  --inst_subs_new                         false
% 3.80/1.02  --inst_eq_res_simp                      false
% 3.80/1.02  --inst_subs_given                       false
% 3.80/1.02  --inst_orphan_elimination               true
% 3.80/1.02  --inst_learning_loop_flag               true
% 3.80/1.02  --inst_learning_start                   3000
% 3.80/1.02  --inst_learning_factor                  2
% 3.80/1.02  --inst_start_prop_sim_after_learn       3
% 3.80/1.02  --inst_sel_renew                        solver
% 3.80/1.02  --inst_lit_activity_flag                true
% 3.80/1.02  --inst_restr_to_given                   false
% 3.80/1.02  --inst_activity_threshold               500
% 3.80/1.02  --inst_out_proof                        true
% 3.80/1.02  
% 3.80/1.02  ------ Resolution Options
% 3.80/1.02  
% 3.80/1.02  --resolution_flag                       false
% 3.80/1.02  --res_lit_sel                           adaptive
% 3.80/1.02  --res_lit_sel_side                      none
% 3.80/1.02  --res_ordering                          kbo
% 3.80/1.02  --res_to_prop_solver                    active
% 3.80/1.02  --res_prop_simpl_new                    false
% 3.80/1.02  --res_prop_simpl_given                  true
% 3.80/1.02  --res_passive_queue_type                priority_queues
% 3.80/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.80/1.02  --res_passive_queues_freq               [15;5]
% 3.80/1.02  --res_forward_subs                      full
% 3.80/1.02  --res_backward_subs                     full
% 3.80/1.02  --res_forward_subs_resolution           true
% 3.80/1.02  --res_backward_subs_resolution          true
% 3.80/1.02  --res_orphan_elimination                true
% 3.80/1.02  --res_time_limit                        2.
% 3.80/1.02  --res_out_proof                         true
% 3.80/1.02  
% 3.80/1.02  ------ Superposition Options
% 3.80/1.02  
% 3.80/1.02  --superposition_flag                    true
% 3.80/1.02  --sup_passive_queue_type                priority_queues
% 3.80/1.02  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.80/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.80/1.02  --demod_completeness_check              fast
% 3.80/1.02  --demod_use_ground                      true
% 3.80/1.02  --sup_to_prop_solver                    active
% 3.80/1.02  --sup_prop_simpl_new                    false
% 3.80/1.02  --sup_prop_simpl_given                  false
% 3.80/1.02  --sup_fun_splitting                     true
% 3.80/1.02  --sup_smt_interval                      10000
% 3.80/1.02  
% 3.80/1.02  ------ Superposition Simplification Setup
% 3.80/1.02  
% 3.80/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.80/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.80/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.80/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.80/1.02  --sup_full_triv                         [TrivRules]
% 3.80/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.80/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.80/1.02  --sup_immed_triv                        [TrivRules]
% 3.80/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/1.02  --sup_immed_bw_main                     []
% 3.80/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.80/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.80/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/1.02  --sup_input_bw                          [BwDemod;BwSubsumption]
% 3.80/1.02  
% 3.80/1.02  ------ Combination Options
% 3.80/1.02  
% 3.80/1.02  --comb_res_mult                         1
% 3.80/1.02  --comb_sup_mult                         1
% 3.80/1.02  --comb_inst_mult                        1000000
% 3.80/1.02  
% 3.80/1.02  ------ Debug Options
% 3.80/1.02  
% 3.80/1.02  --dbg_backtrace                         false
% 3.80/1.02  --dbg_dump_prop_clauses                 false
% 3.80/1.02  --dbg_dump_prop_clauses_file            -
% 3.80/1.02  --dbg_out_stat                          false
% 3.80/1.02  
% 3.80/1.02  
% 3.80/1.02  
% 3.80/1.02  
% 3.80/1.02  ------ Proving...
% 3.80/1.02  
% 3.80/1.02  
% 3.80/1.02  % SZS status Theorem for theBenchmark.p
% 3.80/1.02  
% 3.80/1.02   Resolution empty clause
% 3.80/1.02  
% 3.80/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.80/1.02  
% 3.80/1.02  fof(f7,axiom,(
% 3.80/1.02    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f31,plain,(
% 3.80/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.80/1.02    inference(cnf_transformation,[],[f7])).
% 3.80/1.02  
% 3.80/1.02  fof(f2,axiom,(
% 3.80/1.02    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f19,plain,(
% 3.80/1.02    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.80/1.02    inference(rectify,[],[f2])).
% 3.80/1.02  
% 3.80/1.02  fof(f26,plain,(
% 3.80/1.02    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.80/1.02    inference(cnf_transformation,[],[f19])).
% 3.80/1.02  
% 3.80/1.02  fof(f8,axiom,(
% 3.80/1.02    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f32,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 3.80/1.02    inference(cnf_transformation,[],[f8])).
% 3.80/1.02  
% 3.80/1.02  fof(f4,axiom,(
% 3.80/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f28,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.80/1.02    inference(cnf_transformation,[],[f4])).
% 3.80/1.02  
% 3.80/1.02  fof(f1,axiom,(
% 3.80/1.02    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f25,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.80/1.02    inference(cnf_transformation,[],[f1])).
% 3.80/1.02  
% 3.80/1.02  fof(f3,axiom,(
% 3.80/1.02    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f27,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 3.80/1.02    inference(cnf_transformation,[],[f3])).
% 3.80/1.02  
% 3.80/1.02  fof(f10,axiom,(
% 3.80/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f34,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.80/1.02    inference(cnf_transformation,[],[f10])).
% 3.80/1.02  
% 3.80/1.02  fof(f42,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.80/1.02    inference(definition_unfolding,[],[f27,f34])).
% 3.80/1.02  
% 3.80/1.02  fof(f44,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 3.80/1.02    inference(definition_unfolding,[],[f25,f42,f42])).
% 3.80/1.02  
% 3.80/1.02  fof(f6,axiom,(
% 3.80/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f30,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.80/1.02    inference(cnf_transformation,[],[f6])).
% 3.80/1.02  
% 3.80/1.02  fof(f9,axiom,(
% 3.80/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f33,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.80/1.02    inference(cnf_transformation,[],[f9])).
% 3.80/1.02  
% 3.80/1.02  fof(f45,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.80/1.02    inference(definition_unfolding,[],[f33,f34])).
% 3.80/1.02  
% 3.80/1.02  fof(f5,axiom,(
% 3.80/1.02    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f29,plain,(
% 3.80/1.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.80/1.02    inference(cnf_transformation,[],[f5])).
% 3.80/1.02  
% 3.80/1.02  fof(f11,axiom,(
% 3.80/1.02    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f35,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.80/1.02    inference(cnf_transformation,[],[f11])).
% 3.80/1.02  
% 3.80/1.02  fof(f46,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 3.80/1.02    inference(definition_unfolding,[],[f35,f34])).
% 3.80/1.02  
% 3.80/1.02  fof(f13,axiom,(
% 3.80/1.02    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f37,plain,(
% 3.80/1.02    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.80/1.02    inference(cnf_transformation,[],[f13])).
% 3.80/1.02  
% 3.80/1.02  fof(f14,axiom,(
% 3.80/1.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f20,plain,(
% 3.80/1.02    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 3.80/1.02    inference(unused_predicate_definition_removal,[],[f14])).
% 3.80/1.02  
% 3.80/1.02  fof(f21,plain,(
% 3.80/1.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 3.80/1.02    inference(ennf_transformation,[],[f20])).
% 3.80/1.02  
% 3.80/1.02  fof(f38,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.80/1.02    inference(cnf_transformation,[],[f21])).
% 3.80/1.02  
% 3.80/1.02  fof(f15,axiom,(
% 3.80/1.02    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f39,plain,(
% 3.80/1.02    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.80/1.02    inference(cnf_transformation,[],[f15])).
% 3.80/1.02  
% 3.80/1.02  fof(f48,plain,(
% 3.80/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2)))) )),
% 3.80/1.02    inference(definition_unfolding,[],[f39,f42,f42,f42,f42])).
% 3.80/1.02  
% 3.80/1.02  fof(f16,axiom,(
% 3.80/1.02    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f40,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.80/1.02    inference(cnf_transformation,[],[f16])).
% 3.80/1.02  
% 3.80/1.02  fof(f43,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) )),
% 3.80/1.02    inference(definition_unfolding,[],[f40,f42,f42,f34])).
% 3.80/1.02  
% 3.80/1.02  fof(f17,conjecture,(
% 3.80/1.02    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f18,negated_conjecture,(
% 3.80/1.02    ~! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.80/1.02    inference(negated_conjecture,[],[f17])).
% 3.80/1.02  
% 3.80/1.02  fof(f22,plain,(
% 3.80/1.02    ? [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_xboole_0(X0,X1)),
% 3.80/1.02    inference(ennf_transformation,[],[f18])).
% 3.80/1.02  
% 3.80/1.02  fof(f23,plain,(
% 3.80/1.02    ? [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_xboole_0(X0,X1) => k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1)),
% 3.80/1.02    introduced(choice_axiom,[])).
% 3.80/1.02  
% 3.80/1.02  fof(f24,plain,(
% 3.80/1.02    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1)),
% 3.80/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 3.80/1.02  
% 3.80/1.02  fof(f41,plain,(
% 3.80/1.02    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1)),
% 3.80/1.02    inference(cnf_transformation,[],[f24])).
% 3.80/1.02  
% 3.80/1.02  fof(f49,plain,(
% 3.80/1.02    k2_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))))),
% 3.80/1.02    inference(definition_unfolding,[],[f41,f42])).
% 3.80/1.02  
% 3.80/1.02  cnf(c_6,plain,
% 3.80/1.02      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.80/1.02      inference(cnf_transformation,[],[f31]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_2,plain,
% 3.80/1.02      ( k2_xboole_0(X0,X0) = X0 ),
% 3.80/1.02      inference(cnf_transformation,[],[f26]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_7,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.80/1.02      inference(cnf_transformation,[],[f32]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_79,plain,
% 3.80/1.02      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_2,c_7]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_116,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_6,c_79]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_3,plain,
% 3.80/1.02      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.80/1.02      inference(cnf_transformation,[],[f28]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_117,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_116,c_3]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_257,plain,
% 3.80/1.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_117,c_3]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_82,plain,
% 3.80/1.02      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_79,c_3]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_84,plain,
% 3.80/1.02      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.80/1.02      inference(light_normalisation,[status(thm)],[c_82,c_2]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_259,plain,
% 3.80/1.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_257,c_84]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 3.80/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_640,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1))) = k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1)))) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_259,c_1]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_5,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 3.80/1.02      inference(cnf_transformation,[],[f30]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_8,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.80/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_129,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_5,c_8]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_150,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.80/1.02      inference(light_normalisation,[status(thm)],[c_129,c_5]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_642,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0)))) = k4_xboole_0(X1,X0) ),
% 3.80/1.02      inference(light_normalisation,[status(thm)],[c_640,c_5,c_150]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_4,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.80/1.02      inference(cnf_transformation,[],[f29]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_90,plain,
% 3.80/1.02      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_5,c_3]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_93,plain,
% 3.80/1.02      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.80/1.02      inference(light_normalisation,[status(thm)],[c_90,c_3]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_643,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_642,c_4,c_93,c_117]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_9,plain,
% 3.80/1.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 3.80/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_345,plain,
% 3.80/1.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_9,c_93]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_154,plain,
% 3.80/1.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_357,plain,
% 3.80/1.02      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 3.80/1.02      inference(light_normalisation,[status(thm)],[c_345,c_154]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_249,plain,
% 3.80/1.02      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_9,c_117]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_285,plain,
% 3.80/1.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_249,c_6]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_11,plain,
% 3.80/1.02      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 3.80/1.02      inference(cnf_transformation,[],[f37]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_12,plain,
% 3.80/1.02      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.80/1.02      inference(cnf_transformation,[],[f38]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_54,plain,
% 3.80/1.02      ( X0 != X1 | k4_xboole_0(X2,X1) != X3 | k4_xboole_0(X3,X0) = X3 ),
% 3.80/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_12]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_55,plain,
% 3.80/1.02      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 3.80/1.02      inference(unflattening,[status(thm)],[c_54]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_96,plain,
% 3.80/1.02      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_79,c_55]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_97,plain,
% 3.80/1.02      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.80/1.02      inference(light_normalisation,[status(thm)],[c_96,c_79]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_298,plain,
% 3.80/1.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_285,c_6,c_97]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_738,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k1_xboole_0 ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_298,c_6]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1344,plain,
% 3.80/1.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_357,c_738]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1665,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_1344,c_6]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1702,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X1,X0))) = k1_xboole_0 ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_93,c_1665]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_13,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) ),
% 3.80/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_77,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2)))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_13,c_6]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_78,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_77,c_6]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_5239,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X0))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X0))))))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k2_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0))) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_1702,c_78]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_558,plain,
% 3.80/1.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_1,c_357]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_5242,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X0))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X0))))))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0))) ),
% 3.80/1.02      inference(light_normalisation,[status(thm)],[c_5239,c_558]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_288,plain,
% 3.80/1.02      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_249,c_3]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_292,plain,
% 3.80/1.02      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.80/1.02      inference(light_normalisation,[status(thm)],[c_288,c_84]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_888,plain,
% 3.80/1.02      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_643,c_3]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_890,plain,
% 3.80/1.02      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 3.80/1.02      inference(light_normalisation,[status(thm)],[c_888,c_3]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_89,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_2320,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_1,c_89]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_0,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k2_xboole_0(X0,X1) ),
% 3.80/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_74,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k2_xboole_0(X0,X1) ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_0,c_6]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_75,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k2_xboole_0(X0,X1) ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_74,c_3]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_76,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X1)))) = k2_xboole_0(X0,X1) ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_75,c_3]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_358,plain,
% 3.80/1.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_76,c_4,c_117]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_866,plain,
% 3.80/1.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_358,c_643]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_978,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))))))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0))) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_117,c_78]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1323,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 3.80/1.02      inference(demodulation,
% 3.80/1.02                [status(thm)],
% 3.80/1.02                [c_978,c_4,c_8,c_84,c_93,c_117,c_292,c_357,c_643]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1381,plain,
% 3.80/1.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k2_xboole_0(X0,X1)) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_358,c_890]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1395,plain,
% 3.80/1.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_890,c_358]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1417,plain,
% 3.80/1.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))) = k2_xboole_0(X0,X1) ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_1395,c_890]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1418,plain,
% 3.80/1.02      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 3.80/1.02      inference(light_normalisation,[status(thm)],[c_1417,c_4,c_7,c_643]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1424,plain,
% 3.80/1.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_1381,c_1418]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1425,plain,
% 3.80/1.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_1424,c_357]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_2423,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 3.80/1.02      inference(light_normalisation,[status(thm)],[c_2320,c_866,c_1323,c_1425]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_5243,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.80/1.02      inference(demodulation,
% 3.80/1.02                [status(thm)],
% 3.80/1.02                [c_5242,c_4,c_7,c_8,c_84,c_292,c_643,c_890,c_2423]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_7649,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_643,c_5243]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_7818,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 3.80/1.02      inference(light_normalisation,[status(thm)],[c_7649,c_4,c_7,c_89]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_14,negated_conjecture,
% 3.80/1.02      ( k2_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ),
% 3.80/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_73,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) != k2_xboole_0(sK0,sK1) ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_14,c_3]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_8068,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK0)) != k2_xboole_0(sK0,sK1) ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_7818,c_73]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_8070,plain,
% 3.80/1.02      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_8068,c_4,c_79]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_8071,plain,
% 3.80/1.02      ( $false ),
% 3.80/1.02      inference(equality_resolution_simp,[status(thm)],[c_8070]) ).
% 3.80/1.02  
% 3.80/1.02  
% 3.80/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.80/1.02  
% 3.80/1.02  ------                               Statistics
% 3.80/1.02  
% 3.80/1.02  ------ General
% 3.80/1.02  
% 3.80/1.02  abstr_ref_over_cycles:                  0
% 3.80/1.02  abstr_ref_under_cycles:                 0
% 3.80/1.02  gc_basic_clause_elim:                   0
% 3.80/1.02  forced_gc_time:                         0
% 3.80/1.02  parsing_time:                           0.007
% 3.80/1.02  unif_index_cands_time:                  0.
% 3.80/1.02  unif_index_add_time:                    0.
% 3.80/1.02  orderings_time:                         0.
% 3.80/1.02  out_proof_time:                         0.01
% 3.80/1.02  total_time:                             0.333
% 3.80/1.02  num_of_symbols:                         37
% 3.80/1.02  num_of_terms:                           16891
% 3.80/1.02  
% 3.80/1.02  ------ Preprocessing
% 3.80/1.02  
% 3.80/1.02  num_of_splits:                          0
% 3.80/1.02  num_of_split_atoms:                     0
% 3.80/1.02  num_of_reused_defs:                     0
% 3.80/1.02  num_eq_ax_congr_red:                    1
% 3.80/1.02  num_of_sem_filtered_clauses:            0
% 3.80/1.02  num_of_subtypes:                        0
% 3.80/1.02  monotx_restored_types:                  0
% 3.80/1.02  sat_num_of_epr_types:                   0
% 3.80/1.02  sat_num_of_non_cyclic_types:            0
% 3.80/1.02  sat_guarded_non_collapsed_types:        0
% 3.80/1.02  num_pure_diseq_elim:                    0
% 3.80/1.02  simp_replaced_by:                       0
% 3.80/1.02  res_preprocessed:                       47
% 3.80/1.02  prep_upred:                             0
% 3.80/1.02  prep_unflattend:                        2
% 3.80/1.02  smt_new_axioms:                         0
% 3.80/1.02  pred_elim_cands:                        0
% 3.80/1.02  pred_elim:                              1
% 3.80/1.02  pred_elim_cl:                           1
% 3.80/1.02  pred_elim_cycles:                       2
% 3.80/1.02  merged_defs:                            0
% 3.80/1.02  merged_defs_ncl:                        0
% 3.80/1.02  bin_hyper_res:                          0
% 3.80/1.02  prep_cycles:                            3
% 3.80/1.02  pred_elim_time:                         0.
% 3.80/1.02  splitting_time:                         0.
% 3.80/1.02  sem_filter_time:                        0.
% 3.80/1.02  monotx_time:                            0.
% 3.80/1.02  subtype_inf_time:                       0.
% 3.80/1.02  
% 3.80/1.02  ------ Problem properties
% 3.80/1.02  
% 3.80/1.02  clauses:                                14
% 3.80/1.02  conjectures:                            1
% 3.80/1.02  epr:                                    0
% 3.80/1.02  horn:                                   14
% 3.80/1.02  ground:                                 1
% 3.80/1.02  unary:                                  14
% 3.80/1.02  binary:                                 0
% 3.80/1.02  lits:                                   14
% 3.80/1.02  lits_eq:                                14
% 3.80/1.02  fd_pure:                                0
% 3.80/1.02  fd_pseudo:                              0
% 3.80/1.02  fd_cond:                                0
% 3.80/1.02  fd_pseudo_cond:                         0
% 3.80/1.02  ac_symbols:                             0
% 3.80/1.02  
% 3.80/1.02  ------ Propositional Solver
% 3.80/1.02  
% 3.80/1.02  prop_solver_calls:                      17
% 3.80/1.02  prop_fast_solver_calls:                 109
% 3.80/1.02  smt_solver_calls:                       0
% 3.80/1.02  smt_fast_solver_calls:                  0
% 3.80/1.02  prop_num_of_clauses:                    160
% 3.80/1.02  prop_preprocess_simplified:             684
% 3.80/1.02  prop_fo_subsumed:                       0
% 3.80/1.02  prop_solver_time:                       0.
% 3.80/1.02  smt_solver_time:                        0.
% 3.80/1.02  smt_fast_solver_time:                   0.
% 3.80/1.02  prop_fast_solver_time:                  0.
% 3.80/1.02  prop_unsat_core_time:                   0.
% 3.80/1.02  
% 3.80/1.02  ------ QBF
% 3.80/1.02  
% 3.80/1.02  qbf_q_res:                              0
% 3.80/1.02  qbf_num_tautologies:                    0
% 3.80/1.02  qbf_prep_cycles:                        0
% 3.80/1.02  
% 3.80/1.02  ------ BMC1
% 3.80/1.02  
% 3.80/1.02  bmc1_current_bound:                     -1
% 3.80/1.02  bmc1_last_solved_bound:                 -1
% 3.80/1.02  bmc1_unsat_core_size:                   -1
% 3.80/1.02  bmc1_unsat_core_parents_size:           -1
% 3.80/1.02  bmc1_merge_next_fun:                    0
% 3.80/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.80/1.02  
% 3.80/1.02  ------ Instantiation
% 3.80/1.02  
% 3.80/1.02  inst_num_of_clauses:                    0
% 3.80/1.02  inst_num_in_passive:                    0
% 3.80/1.02  inst_num_in_active:                     0
% 3.80/1.02  inst_num_in_unprocessed:                0
% 3.80/1.02  inst_num_of_loops:                      0
% 3.80/1.02  inst_num_of_learning_restarts:          0
% 3.80/1.02  inst_num_moves_active_passive:          0
% 3.80/1.02  inst_lit_activity:                      0
% 3.80/1.02  inst_lit_activity_moves:                0
% 3.80/1.02  inst_num_tautologies:                   0
% 3.80/1.02  inst_num_prop_implied:                  0
% 3.80/1.02  inst_num_existing_simplified:           0
% 3.80/1.02  inst_num_eq_res_simplified:             0
% 3.80/1.02  inst_num_child_elim:                    0
% 3.80/1.02  inst_num_of_dismatching_blockings:      0
% 3.80/1.02  inst_num_of_non_proper_insts:           0
% 3.80/1.02  inst_num_of_duplicates:                 0
% 3.80/1.02  inst_inst_num_from_inst_to_res:         0
% 3.80/1.02  inst_dismatching_checking_time:         0.
% 3.80/1.02  
% 3.80/1.02  ------ Resolution
% 3.80/1.02  
% 3.80/1.02  res_num_of_clauses:                     0
% 3.80/1.02  res_num_in_passive:                     0
% 3.80/1.02  res_num_in_active:                      0
% 3.80/1.02  res_num_of_loops:                       50
% 3.80/1.02  res_forward_subset_subsumed:            0
% 3.80/1.02  res_backward_subset_subsumed:           0
% 3.80/1.02  res_forward_subsumed:                   0
% 3.80/1.02  res_backward_subsumed:                  0
% 3.80/1.02  res_forward_subsumption_resolution:     0
% 3.80/1.02  res_backward_subsumption_resolution:    0
% 3.80/1.02  res_clause_to_clause_subsumption:       16598
% 3.80/1.02  res_orphan_elimination:                 0
% 3.80/1.02  res_tautology_del:                      0
% 3.80/1.02  res_num_eq_res_simplified:              0
% 3.80/1.02  res_num_sel_changes:                    0
% 3.80/1.02  res_moves_from_active_to_pass:          0
% 3.80/1.02  
% 3.80/1.02  ------ Superposition
% 3.80/1.02  
% 3.80/1.02  sup_time_total:                         0.
% 3.80/1.02  sup_time_generating:                    0.
% 3.80/1.02  sup_time_sim_full:                      0.
% 3.80/1.02  sup_time_sim_immed:                     0.
% 3.80/1.02  
% 3.80/1.02  sup_num_of_clauses:                     941
% 3.80/1.02  sup_num_in_active:                      71
% 3.80/1.02  sup_num_in_passive:                     870
% 3.80/1.02  sup_num_of_loops:                       82
% 3.80/1.02  sup_fw_superposition:                   3015
% 3.80/1.02  sup_bw_superposition:                   2531
% 3.80/1.02  sup_immediate_simplified:               2500
% 3.80/1.02  sup_given_eliminated:                   0
% 3.80/1.02  comparisons_done:                       0
% 3.80/1.02  comparisons_avoided:                    0
% 3.80/1.02  
% 3.80/1.02  ------ Simplifications
% 3.80/1.02  
% 3.80/1.02  
% 3.80/1.02  sim_fw_subset_subsumed:                 0
% 3.80/1.02  sim_bw_subset_subsumed:                 0
% 3.80/1.02  sim_fw_subsumed:                        635
% 3.80/1.02  sim_bw_subsumed:                        14
% 3.80/1.02  sim_fw_subsumption_res:                 0
% 3.80/1.02  sim_bw_subsumption_res:                 0
% 3.80/1.02  sim_tautology_del:                      0
% 3.80/1.02  sim_eq_tautology_del:                   775
% 3.80/1.02  sim_eq_res_simp:                        0
% 3.80/1.02  sim_fw_demodulated:                     1545
% 3.80/1.02  sim_bw_demodulated:                     8
% 3.80/1.02  sim_light_normalised:                   854
% 3.80/1.02  sim_joinable_taut:                      0
% 3.80/1.02  sim_joinable_simp:                      0
% 3.80/1.02  sim_ac_normalised:                      0
% 3.80/1.02  sim_smt_subsumption:                    0
% 3.80/1.02  
%------------------------------------------------------------------------------
