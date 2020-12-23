%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:04 EST 2020

% Result     : Theorem 15.86s
% Output     : CNFRefutation 15.86s
% Verified   : 
% Statistics : Number of formulae       :  141 (4339 expanded)
%              Number of clauses        :  105 (2009 expanded)
%              Number of leaves         :   14 (1080 expanded)
%              Depth                    :   32
%              Number of atoms          :  156 (5012 expanded)
%              Number of equality atoms :  141 (4427 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f21,f31,f31])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f13,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f16,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f18,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).

fof(f33,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f33,f31,f22,f22])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f26,f31])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_7,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_253,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_950,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_253,c_1])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_255,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_256,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_255,c_6])).

cnf(c_310,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_256])).

cnf(c_317,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_310,c_7])).

cnf(c_10,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_320,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_317,c_10])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_581,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_320,c_8])).

cnf(c_584,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_581,c_10])).

cnf(c_953,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_950,c_6,c_584])).

cnf(c_1835,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_253,c_953])).

cnf(c_647,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_584])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_50,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_88,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | k2_xboole_0(X0,X1) = X1 ),
    inference(resolution,[status(thm)],[c_50,c_4])).

cnf(c_670,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_647,c_88])).

cnf(c_1318,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_670])).

cnf(c_1878,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_1835,c_1318])).

cnf(c_2668,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_1878,c_8])).

cnf(c_11,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_209,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_11])).

cnf(c_69783,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_2668,c_209])).

cnf(c_583,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_320,c_8])).

cnf(c_967,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_253,c_583])).

cnf(c_963,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_583])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_485,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_4793,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_963,c_485])).

cnf(c_947,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_253,c_8])).

cnf(c_954,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_947,c_8])).

cnf(c_2647,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_647,c_1878])).

cnf(c_654,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_584,c_88])).

cnf(c_1223,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_654])).

cnf(c_2689,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2647,c_1223])).

cnf(c_4798,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) = k4_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_4793,c_954,c_2689])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_97,plain,
    ( X0 != X1
    | k4_xboole_0(X0,k4_xboole_0(X0,X2)) != X3
    | k2_xboole_0(X3,X1) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_98,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_97])).

cnf(c_763,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_98])).

cnf(c_785,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_763,c_485])).

cnf(c_801,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_785,c_7])).

cnf(c_806,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_801,c_320])).

cnf(c_891,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_806,c_8])).

cnf(c_898,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_891,c_8,c_10])).

cnf(c_1594,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_670,c_898])).

cnf(c_4799,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4798,c_1594])).

cnf(c_458,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_17248,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k4_xboole_0(X0,X1)))),X2) = k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X1)),k2_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[status(thm)],[c_4799,c_458])).

cnf(c_17325,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_17248,c_963,c_2689])).

cnf(c_17326,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_17325,c_310])).

cnf(c_468,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_17282,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4799,c_468])).

cnf(c_3115,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_2689,c_8])).

cnf(c_3129,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_3115,c_310])).

cnf(c_13177,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_3129,c_8])).

cnf(c_17297,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X0),X0),X1) ),
    inference(demodulation,[status(thm)],[c_17282,c_256,c_13177])).

cnf(c_17327,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X0),X0),X1) ),
    inference(demodulation,[status(thm)],[c_17326,c_17297])).

cnf(c_17329,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X0) = k4_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_17327,c_7,c_9])).

cnf(c_24827,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1))) ),
    inference(superposition,[status(thm)],[c_17329,c_1])).

cnf(c_876,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_806])).

cnf(c_1539,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_876,c_8])).

cnf(c_24873,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_24827,c_6,c_1539])).

cnf(c_30263,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1)),k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_967,c_24873])).

cnf(c_793,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_785])).

cnf(c_3611,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_670,c_793])).

cnf(c_3663,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_3611,c_647,c_1223])).

cnf(c_5052,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_967,c_485])).

cnf(c_5058,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5052,c_2689,c_4799])).

cnf(c_31198,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_30263,c_3663,c_5058])).

cnf(c_31199,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_31198,c_2689])).

cnf(c_2132,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_670,c_1223])).

cnf(c_2141,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_1223,c_1223])).

cnf(c_2143,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1223,c_670])).

cnf(c_2155,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2143,c_1223])).

cnf(c_2157,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2141,c_2155])).

cnf(c_2162,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2132,c_2157])).

cnf(c_31958,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_31199,c_2162])).

cnf(c_32073,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_31958,c_2162])).

cnf(c_2145,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1223,c_647])).

cnf(c_978,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_583,c_8])).

cnf(c_464,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_8,c_8])).

cnf(c_473,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_464,c_8])).

cnf(c_982,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X1)),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_978,c_10,c_473])).

cnf(c_5434,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0),X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2145,c_982])).

cnf(c_3726,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3663,c_2157])).

cnf(c_804,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_785,c_0])).

cnf(c_858,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_804])).

cnf(c_1360,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_584,c_858])).

cnf(c_1379,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1360,c_6])).

cnf(c_2895,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_2157,c_1379])).

cnf(c_2923,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2895,c_2157])).

cnf(c_3763,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_3726,c_2923])).

cnf(c_5486,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5434,c_473,c_3763])).

cnf(c_18147,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_785,c_5486])).

cnf(c_36202,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_32073,c_18147])).

cnf(c_69784,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_69783,c_256,c_36202])).

cnf(c_345,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_69784,c_345])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.86/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.86/2.50  
% 15.86/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.86/2.50  
% 15.86/2.50  ------  iProver source info
% 15.86/2.50  
% 15.86/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.86/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.86/2.50  git: non_committed_changes: false
% 15.86/2.50  git: last_make_outside_of_git: false
% 15.86/2.50  
% 15.86/2.50  ------ 
% 15.86/2.50  
% 15.86/2.50  ------ Input Options
% 15.86/2.50  
% 15.86/2.50  --out_options                           all
% 15.86/2.50  --tptp_safe_out                         true
% 15.86/2.50  --problem_path                          ""
% 15.86/2.50  --include_path                          ""
% 15.86/2.50  --clausifier                            res/vclausify_rel
% 15.86/2.50  --clausifier_options                    ""
% 15.86/2.50  --stdin                                 false
% 15.86/2.50  --stats_out                             all
% 15.86/2.50  
% 15.86/2.50  ------ General Options
% 15.86/2.50  
% 15.86/2.50  --fof                                   false
% 15.86/2.50  --time_out_real                         305.
% 15.86/2.50  --time_out_virtual                      -1.
% 15.86/2.50  --symbol_type_check                     false
% 15.86/2.50  --clausify_out                          false
% 15.86/2.50  --sig_cnt_out                           false
% 15.86/2.50  --trig_cnt_out                          false
% 15.86/2.50  --trig_cnt_out_tolerance                1.
% 15.86/2.50  --trig_cnt_out_sk_spl                   false
% 15.86/2.50  --abstr_cl_out                          false
% 15.86/2.50  
% 15.86/2.50  ------ Global Options
% 15.86/2.50  
% 15.86/2.50  --schedule                              default
% 15.86/2.50  --add_important_lit                     false
% 15.86/2.50  --prop_solver_per_cl                    1000
% 15.86/2.50  --min_unsat_core                        false
% 15.86/2.50  --soft_assumptions                      false
% 15.86/2.50  --soft_lemma_size                       3
% 15.86/2.50  --prop_impl_unit_size                   0
% 15.86/2.50  --prop_impl_unit                        []
% 15.86/2.50  --share_sel_clauses                     true
% 15.86/2.50  --reset_solvers                         false
% 15.86/2.50  --bc_imp_inh                            [conj_cone]
% 15.86/2.50  --conj_cone_tolerance                   3.
% 15.86/2.50  --extra_neg_conj                        none
% 15.86/2.50  --large_theory_mode                     true
% 15.86/2.50  --prolific_symb_bound                   200
% 15.86/2.50  --lt_threshold                          2000
% 15.86/2.50  --clause_weak_htbl                      true
% 15.86/2.50  --gc_record_bc_elim                     false
% 15.86/2.50  
% 15.86/2.50  ------ Preprocessing Options
% 15.86/2.50  
% 15.86/2.50  --preprocessing_flag                    true
% 15.86/2.50  --time_out_prep_mult                    0.1
% 15.86/2.50  --splitting_mode                        input
% 15.86/2.50  --splitting_grd                         true
% 15.86/2.50  --splitting_cvd                         false
% 15.86/2.50  --splitting_cvd_svl                     false
% 15.86/2.50  --splitting_nvd                         32
% 15.86/2.50  --sub_typing                            true
% 15.86/2.50  --prep_gs_sim                           true
% 15.86/2.50  --prep_unflatten                        true
% 15.86/2.50  --prep_res_sim                          true
% 15.86/2.50  --prep_upred                            true
% 15.86/2.50  --prep_sem_filter                       exhaustive
% 15.86/2.50  --prep_sem_filter_out                   false
% 15.86/2.50  --pred_elim                             true
% 15.86/2.50  --res_sim_input                         true
% 15.86/2.50  --eq_ax_congr_red                       true
% 15.86/2.50  --pure_diseq_elim                       true
% 15.86/2.50  --brand_transform                       false
% 15.86/2.50  --non_eq_to_eq                          false
% 15.86/2.50  --prep_def_merge                        true
% 15.86/2.50  --prep_def_merge_prop_impl              false
% 15.86/2.50  --prep_def_merge_mbd                    true
% 15.86/2.50  --prep_def_merge_tr_red                 false
% 15.86/2.50  --prep_def_merge_tr_cl                  false
% 15.86/2.50  --smt_preprocessing                     true
% 15.86/2.50  --smt_ac_axioms                         fast
% 15.86/2.50  --preprocessed_out                      false
% 15.86/2.50  --preprocessed_stats                    false
% 15.86/2.50  
% 15.86/2.50  ------ Abstraction refinement Options
% 15.86/2.50  
% 15.86/2.50  --abstr_ref                             []
% 15.86/2.50  --abstr_ref_prep                        false
% 15.86/2.50  --abstr_ref_until_sat                   false
% 15.86/2.50  --abstr_ref_sig_restrict                funpre
% 15.86/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.86/2.50  --abstr_ref_under                       []
% 15.86/2.50  
% 15.86/2.50  ------ SAT Options
% 15.86/2.50  
% 15.86/2.50  --sat_mode                              false
% 15.86/2.50  --sat_fm_restart_options                ""
% 15.86/2.50  --sat_gr_def                            false
% 15.86/2.50  --sat_epr_types                         true
% 15.86/2.50  --sat_non_cyclic_types                  false
% 15.86/2.50  --sat_finite_models                     false
% 15.86/2.50  --sat_fm_lemmas                         false
% 15.86/2.50  --sat_fm_prep                           false
% 15.86/2.50  --sat_fm_uc_incr                        true
% 15.86/2.50  --sat_out_model                         small
% 15.86/2.50  --sat_out_clauses                       false
% 15.86/2.50  
% 15.86/2.50  ------ QBF Options
% 15.86/2.50  
% 15.86/2.50  --qbf_mode                              false
% 15.86/2.50  --qbf_elim_univ                         false
% 15.86/2.50  --qbf_dom_inst                          none
% 15.86/2.50  --qbf_dom_pre_inst                      false
% 15.86/2.50  --qbf_sk_in                             false
% 15.86/2.50  --qbf_pred_elim                         true
% 15.86/2.50  --qbf_split                             512
% 15.86/2.50  
% 15.86/2.50  ------ BMC1 Options
% 15.86/2.50  
% 15.86/2.50  --bmc1_incremental                      false
% 15.86/2.50  --bmc1_axioms                           reachable_all
% 15.86/2.50  --bmc1_min_bound                        0
% 15.86/2.50  --bmc1_max_bound                        -1
% 15.86/2.50  --bmc1_max_bound_default                -1
% 15.86/2.50  --bmc1_symbol_reachability              true
% 15.86/2.50  --bmc1_property_lemmas                  false
% 15.86/2.50  --bmc1_k_induction                      false
% 15.86/2.50  --bmc1_non_equiv_states                 false
% 15.86/2.50  --bmc1_deadlock                         false
% 15.86/2.50  --bmc1_ucm                              false
% 15.86/2.50  --bmc1_add_unsat_core                   none
% 15.86/2.50  --bmc1_unsat_core_children              false
% 15.86/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.86/2.50  --bmc1_out_stat                         full
% 15.86/2.50  --bmc1_ground_init                      false
% 15.86/2.50  --bmc1_pre_inst_next_state              false
% 15.86/2.50  --bmc1_pre_inst_state                   false
% 15.86/2.50  --bmc1_pre_inst_reach_state             false
% 15.86/2.50  --bmc1_out_unsat_core                   false
% 15.86/2.50  --bmc1_aig_witness_out                  false
% 15.86/2.50  --bmc1_verbose                          false
% 15.86/2.50  --bmc1_dump_clauses_tptp                false
% 15.86/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.86/2.50  --bmc1_dump_file                        -
% 15.86/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.86/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.86/2.50  --bmc1_ucm_extend_mode                  1
% 15.86/2.50  --bmc1_ucm_init_mode                    2
% 15.86/2.50  --bmc1_ucm_cone_mode                    none
% 15.86/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.86/2.50  --bmc1_ucm_relax_model                  4
% 15.86/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.86/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.86/2.50  --bmc1_ucm_layered_model                none
% 15.86/2.50  --bmc1_ucm_max_lemma_size               10
% 15.86/2.50  
% 15.86/2.50  ------ AIG Options
% 15.86/2.50  
% 15.86/2.50  --aig_mode                              false
% 15.86/2.50  
% 15.86/2.50  ------ Instantiation Options
% 15.86/2.50  
% 15.86/2.50  --instantiation_flag                    true
% 15.86/2.50  --inst_sos_flag                         true
% 15.86/2.50  --inst_sos_phase                        true
% 15.86/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.86/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.86/2.50  --inst_lit_sel_side                     num_symb
% 15.86/2.50  --inst_solver_per_active                1400
% 15.86/2.50  --inst_solver_calls_frac                1.
% 15.86/2.50  --inst_passive_queue_type               priority_queues
% 15.86/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.86/2.50  --inst_passive_queues_freq              [25;2]
% 15.86/2.50  --inst_dismatching                      true
% 15.86/2.50  --inst_eager_unprocessed_to_passive     true
% 15.86/2.50  --inst_prop_sim_given                   true
% 15.86/2.50  --inst_prop_sim_new                     false
% 15.86/2.50  --inst_subs_new                         false
% 15.86/2.50  --inst_eq_res_simp                      false
% 15.86/2.50  --inst_subs_given                       false
% 15.86/2.50  --inst_orphan_elimination               true
% 15.86/2.50  --inst_learning_loop_flag               true
% 15.86/2.50  --inst_learning_start                   3000
% 15.86/2.50  --inst_learning_factor                  2
% 15.86/2.50  --inst_start_prop_sim_after_learn       3
% 15.86/2.50  --inst_sel_renew                        solver
% 15.86/2.50  --inst_lit_activity_flag                true
% 15.86/2.50  --inst_restr_to_given                   false
% 15.86/2.50  --inst_activity_threshold               500
% 15.86/2.50  --inst_out_proof                        true
% 15.86/2.50  
% 15.86/2.50  ------ Resolution Options
% 15.86/2.50  
% 15.86/2.50  --resolution_flag                       true
% 15.86/2.50  --res_lit_sel                           adaptive
% 15.86/2.50  --res_lit_sel_side                      none
% 15.86/2.50  --res_ordering                          kbo
% 15.86/2.50  --res_to_prop_solver                    active
% 15.86/2.50  --res_prop_simpl_new                    false
% 15.86/2.50  --res_prop_simpl_given                  true
% 15.86/2.50  --res_passive_queue_type                priority_queues
% 15.86/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.86/2.50  --res_passive_queues_freq               [15;5]
% 15.86/2.50  --res_forward_subs                      full
% 15.86/2.50  --res_backward_subs                     full
% 15.86/2.50  --res_forward_subs_resolution           true
% 15.86/2.50  --res_backward_subs_resolution          true
% 15.86/2.50  --res_orphan_elimination                true
% 15.86/2.50  --res_time_limit                        2.
% 15.86/2.50  --res_out_proof                         true
% 15.86/2.50  
% 15.86/2.50  ------ Superposition Options
% 15.86/2.50  
% 15.86/2.50  --superposition_flag                    true
% 15.86/2.50  --sup_passive_queue_type                priority_queues
% 15.86/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.86/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.86/2.50  --demod_completeness_check              fast
% 15.86/2.50  --demod_use_ground                      true
% 15.86/2.50  --sup_to_prop_solver                    passive
% 15.86/2.50  --sup_prop_simpl_new                    true
% 15.86/2.50  --sup_prop_simpl_given                  true
% 15.86/2.50  --sup_fun_splitting                     true
% 15.86/2.50  --sup_smt_interval                      50000
% 15.86/2.50  
% 15.86/2.50  ------ Superposition Simplification Setup
% 15.86/2.50  
% 15.86/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.86/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.86/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.86/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.86/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.86/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.86/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.86/2.50  --sup_immed_triv                        [TrivRules]
% 15.86/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.86/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.86/2.50  --sup_immed_bw_main                     []
% 15.86/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.86/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.86/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.86/2.50  --sup_input_bw                          []
% 15.86/2.50  
% 15.86/2.50  ------ Combination Options
% 15.86/2.50  
% 15.86/2.50  --comb_res_mult                         3
% 15.86/2.50  --comb_sup_mult                         2
% 15.86/2.50  --comb_inst_mult                        10
% 15.86/2.50  
% 15.86/2.50  ------ Debug Options
% 15.86/2.50  
% 15.86/2.50  --dbg_backtrace                         false
% 15.86/2.50  --dbg_dump_prop_clauses                 false
% 15.86/2.50  --dbg_dump_prop_clauses_file            -
% 15.86/2.50  --dbg_out_stat                          false
% 15.86/2.50  ------ Parsing...
% 15.86/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.86/2.50  
% 15.86/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.86/2.50  
% 15.86/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.86/2.50  
% 15.86/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.86/2.50  ------ Proving...
% 15.86/2.50  ------ Problem Properties 
% 15.86/2.50  
% 15.86/2.50  
% 15.86/2.50  clauses                                 11
% 15.86/2.50  conjectures                             1
% 15.86/2.50  EPR                                     0
% 15.86/2.50  Horn                                    11
% 15.86/2.50  unary                                   10
% 15.86/2.50  binary                                  1
% 15.86/2.50  lits                                    12
% 15.86/2.50  lits eq                                 12
% 15.86/2.50  fd_pure                                 0
% 15.86/2.50  fd_pseudo                               0
% 15.86/2.50  fd_cond                                 0
% 15.86/2.50  fd_pseudo_cond                          0
% 15.86/2.50  AC symbols                              0
% 15.86/2.50  
% 15.86/2.50  ------ Schedule dynamic 5 is on 
% 15.86/2.50  
% 15.86/2.50  ------ pure equality problem: resolution off 
% 15.86/2.50  
% 15.86/2.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.86/2.50  
% 15.86/2.50  
% 15.86/2.50  ------ 
% 15.86/2.50  Current options:
% 15.86/2.50  ------ 
% 15.86/2.50  
% 15.86/2.50  ------ Input Options
% 15.86/2.50  
% 15.86/2.50  --out_options                           all
% 15.86/2.50  --tptp_safe_out                         true
% 15.86/2.50  --problem_path                          ""
% 15.86/2.50  --include_path                          ""
% 15.86/2.50  --clausifier                            res/vclausify_rel
% 15.86/2.50  --clausifier_options                    ""
% 15.86/2.50  --stdin                                 false
% 15.86/2.50  --stats_out                             all
% 15.86/2.50  
% 15.86/2.50  ------ General Options
% 15.86/2.50  
% 15.86/2.50  --fof                                   false
% 15.86/2.50  --time_out_real                         305.
% 15.86/2.50  --time_out_virtual                      -1.
% 15.86/2.50  --symbol_type_check                     false
% 15.86/2.50  --clausify_out                          false
% 15.86/2.50  --sig_cnt_out                           false
% 15.86/2.50  --trig_cnt_out                          false
% 15.86/2.50  --trig_cnt_out_tolerance                1.
% 15.86/2.50  --trig_cnt_out_sk_spl                   false
% 15.86/2.50  --abstr_cl_out                          false
% 15.86/2.50  
% 15.86/2.50  ------ Global Options
% 15.86/2.50  
% 15.86/2.50  --schedule                              default
% 15.86/2.50  --add_important_lit                     false
% 15.86/2.50  --prop_solver_per_cl                    1000
% 15.86/2.50  --min_unsat_core                        false
% 15.86/2.50  --soft_assumptions                      false
% 15.86/2.50  --soft_lemma_size                       3
% 15.86/2.50  --prop_impl_unit_size                   0
% 15.86/2.50  --prop_impl_unit                        []
% 15.86/2.50  --share_sel_clauses                     true
% 15.86/2.50  --reset_solvers                         false
% 15.86/2.50  --bc_imp_inh                            [conj_cone]
% 15.86/2.50  --conj_cone_tolerance                   3.
% 15.86/2.50  --extra_neg_conj                        none
% 15.86/2.50  --large_theory_mode                     true
% 15.86/2.50  --prolific_symb_bound                   200
% 15.86/2.50  --lt_threshold                          2000
% 15.86/2.50  --clause_weak_htbl                      true
% 15.86/2.50  --gc_record_bc_elim                     false
% 15.86/2.50  
% 15.86/2.50  ------ Preprocessing Options
% 15.86/2.50  
% 15.86/2.50  --preprocessing_flag                    true
% 15.86/2.50  --time_out_prep_mult                    0.1
% 15.86/2.50  --splitting_mode                        input
% 15.86/2.50  --splitting_grd                         true
% 15.86/2.50  --splitting_cvd                         false
% 15.86/2.50  --splitting_cvd_svl                     false
% 15.86/2.50  --splitting_nvd                         32
% 15.86/2.50  --sub_typing                            true
% 15.86/2.50  --prep_gs_sim                           true
% 15.86/2.50  --prep_unflatten                        true
% 15.86/2.50  --prep_res_sim                          true
% 15.86/2.50  --prep_upred                            true
% 15.86/2.50  --prep_sem_filter                       exhaustive
% 15.86/2.50  --prep_sem_filter_out                   false
% 15.86/2.50  --pred_elim                             true
% 15.86/2.50  --res_sim_input                         true
% 15.86/2.50  --eq_ax_congr_red                       true
% 15.86/2.50  --pure_diseq_elim                       true
% 15.86/2.50  --brand_transform                       false
% 15.86/2.50  --non_eq_to_eq                          false
% 15.86/2.50  --prep_def_merge                        true
% 15.86/2.50  --prep_def_merge_prop_impl              false
% 15.86/2.50  --prep_def_merge_mbd                    true
% 15.86/2.50  --prep_def_merge_tr_red                 false
% 15.86/2.50  --prep_def_merge_tr_cl                  false
% 15.86/2.50  --smt_preprocessing                     true
% 15.86/2.50  --smt_ac_axioms                         fast
% 15.86/2.50  --preprocessed_out                      false
% 15.86/2.50  --preprocessed_stats                    false
% 15.86/2.50  
% 15.86/2.50  ------ Abstraction refinement Options
% 15.86/2.50  
% 15.86/2.50  --abstr_ref                             []
% 15.86/2.50  --abstr_ref_prep                        false
% 15.86/2.50  --abstr_ref_until_sat                   false
% 15.86/2.50  --abstr_ref_sig_restrict                funpre
% 15.86/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.86/2.50  --abstr_ref_under                       []
% 15.86/2.50  
% 15.86/2.50  ------ SAT Options
% 15.86/2.50  
% 15.86/2.50  --sat_mode                              false
% 15.86/2.50  --sat_fm_restart_options                ""
% 15.86/2.50  --sat_gr_def                            false
% 15.86/2.50  --sat_epr_types                         true
% 15.86/2.50  --sat_non_cyclic_types                  false
% 15.86/2.50  --sat_finite_models                     false
% 15.86/2.50  --sat_fm_lemmas                         false
% 15.86/2.50  --sat_fm_prep                           false
% 15.86/2.50  --sat_fm_uc_incr                        true
% 15.86/2.50  --sat_out_model                         small
% 15.86/2.50  --sat_out_clauses                       false
% 15.86/2.50  
% 15.86/2.50  ------ QBF Options
% 15.86/2.50  
% 15.86/2.50  --qbf_mode                              false
% 15.86/2.50  --qbf_elim_univ                         false
% 15.86/2.50  --qbf_dom_inst                          none
% 15.86/2.50  --qbf_dom_pre_inst                      false
% 15.86/2.50  --qbf_sk_in                             false
% 15.86/2.50  --qbf_pred_elim                         true
% 15.86/2.50  --qbf_split                             512
% 15.86/2.50  
% 15.86/2.50  ------ BMC1 Options
% 15.86/2.50  
% 15.86/2.50  --bmc1_incremental                      false
% 15.86/2.50  --bmc1_axioms                           reachable_all
% 15.86/2.50  --bmc1_min_bound                        0
% 15.86/2.50  --bmc1_max_bound                        -1
% 15.86/2.50  --bmc1_max_bound_default                -1
% 15.86/2.50  --bmc1_symbol_reachability              true
% 15.86/2.50  --bmc1_property_lemmas                  false
% 15.86/2.50  --bmc1_k_induction                      false
% 15.86/2.50  --bmc1_non_equiv_states                 false
% 15.86/2.50  --bmc1_deadlock                         false
% 15.86/2.50  --bmc1_ucm                              false
% 15.86/2.50  --bmc1_add_unsat_core                   none
% 15.86/2.50  --bmc1_unsat_core_children              false
% 15.86/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.86/2.50  --bmc1_out_stat                         full
% 15.86/2.50  --bmc1_ground_init                      false
% 15.86/2.50  --bmc1_pre_inst_next_state              false
% 15.86/2.50  --bmc1_pre_inst_state                   false
% 15.86/2.50  --bmc1_pre_inst_reach_state             false
% 15.86/2.50  --bmc1_out_unsat_core                   false
% 15.86/2.50  --bmc1_aig_witness_out                  false
% 15.86/2.50  --bmc1_verbose                          false
% 15.86/2.50  --bmc1_dump_clauses_tptp                false
% 15.86/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.86/2.50  --bmc1_dump_file                        -
% 15.86/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.86/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.86/2.50  --bmc1_ucm_extend_mode                  1
% 15.86/2.50  --bmc1_ucm_init_mode                    2
% 15.86/2.50  --bmc1_ucm_cone_mode                    none
% 15.86/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.86/2.50  --bmc1_ucm_relax_model                  4
% 15.86/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.86/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.86/2.50  --bmc1_ucm_layered_model                none
% 15.86/2.50  --bmc1_ucm_max_lemma_size               10
% 15.86/2.50  
% 15.86/2.50  ------ AIG Options
% 15.86/2.50  
% 15.86/2.50  --aig_mode                              false
% 15.86/2.50  
% 15.86/2.50  ------ Instantiation Options
% 15.86/2.50  
% 15.86/2.50  --instantiation_flag                    true
% 15.86/2.50  --inst_sos_flag                         true
% 15.86/2.50  --inst_sos_phase                        true
% 15.86/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.86/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.86/2.50  --inst_lit_sel_side                     none
% 15.86/2.50  --inst_solver_per_active                1400
% 15.86/2.50  --inst_solver_calls_frac                1.
% 15.86/2.50  --inst_passive_queue_type               priority_queues
% 15.86/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.86/2.50  --inst_passive_queues_freq              [25;2]
% 15.86/2.50  --inst_dismatching                      true
% 15.86/2.50  --inst_eager_unprocessed_to_passive     true
% 15.86/2.50  --inst_prop_sim_given                   true
% 15.86/2.50  --inst_prop_sim_new                     false
% 15.86/2.50  --inst_subs_new                         false
% 15.86/2.50  --inst_eq_res_simp                      false
% 15.86/2.50  --inst_subs_given                       false
% 15.86/2.50  --inst_orphan_elimination               true
% 15.86/2.50  --inst_learning_loop_flag               true
% 15.86/2.50  --inst_learning_start                   3000
% 15.86/2.50  --inst_learning_factor                  2
% 15.86/2.50  --inst_start_prop_sim_after_learn       3
% 15.86/2.50  --inst_sel_renew                        solver
% 15.86/2.50  --inst_lit_activity_flag                true
% 15.86/2.50  --inst_restr_to_given                   false
% 15.86/2.50  --inst_activity_threshold               500
% 15.86/2.50  --inst_out_proof                        true
% 15.86/2.50  
% 15.86/2.50  ------ Resolution Options
% 15.86/2.50  
% 15.86/2.50  --resolution_flag                       false
% 15.86/2.50  --res_lit_sel                           adaptive
% 15.86/2.50  --res_lit_sel_side                      none
% 15.86/2.50  --res_ordering                          kbo
% 15.86/2.50  --res_to_prop_solver                    active
% 15.86/2.50  --res_prop_simpl_new                    false
% 15.86/2.50  --res_prop_simpl_given                  true
% 15.86/2.50  --res_passive_queue_type                priority_queues
% 15.86/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.86/2.50  --res_passive_queues_freq               [15;5]
% 15.86/2.50  --res_forward_subs                      full
% 15.86/2.50  --res_backward_subs                     full
% 15.86/2.50  --res_forward_subs_resolution           true
% 15.86/2.50  --res_backward_subs_resolution          true
% 15.86/2.50  --res_orphan_elimination                true
% 15.86/2.50  --res_time_limit                        2.
% 15.86/2.50  --res_out_proof                         true
% 15.86/2.50  
% 15.86/2.50  ------ Superposition Options
% 15.86/2.50  
% 15.86/2.50  --superposition_flag                    true
% 15.86/2.50  --sup_passive_queue_type                priority_queues
% 15.86/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.86/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.86/2.50  --demod_completeness_check              fast
% 15.86/2.50  --demod_use_ground                      true
% 15.86/2.50  --sup_to_prop_solver                    passive
% 15.86/2.50  --sup_prop_simpl_new                    true
% 15.86/2.50  --sup_prop_simpl_given                  true
% 15.86/2.50  --sup_fun_splitting                     true
% 15.86/2.50  --sup_smt_interval                      50000
% 15.86/2.50  
% 15.86/2.50  ------ Superposition Simplification Setup
% 15.86/2.50  
% 15.86/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.86/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.86/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.86/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.86/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.86/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.86/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.86/2.50  --sup_immed_triv                        [TrivRules]
% 15.86/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.86/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.86/2.50  --sup_immed_bw_main                     []
% 15.86/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.86/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.86/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.86/2.50  --sup_input_bw                          []
% 15.86/2.50  
% 15.86/2.50  ------ Combination Options
% 15.86/2.50  
% 15.86/2.50  --comb_res_mult                         3
% 15.86/2.50  --comb_sup_mult                         2
% 15.86/2.50  --comb_inst_mult                        10
% 15.86/2.50  
% 15.86/2.50  ------ Debug Options
% 15.86/2.50  
% 15.86/2.50  --dbg_backtrace                         false
% 15.86/2.50  --dbg_dump_prop_clauses                 false
% 15.86/2.50  --dbg_dump_prop_clauses_file            -
% 15.86/2.50  --dbg_out_stat                          false
% 15.86/2.50  
% 15.86/2.50  
% 15.86/2.50  
% 15.86/2.50  
% 15.86/2.50  ------ Proving...
% 15.86/2.50  
% 15.86/2.50  
% 15.86/2.50  % SZS status Theorem for theBenchmark.p
% 15.86/2.50  
% 15.86/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.86/2.50  
% 15.86/2.50  fof(f1,axiom,(
% 15.86/2.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.86/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.50  
% 15.86/2.50  fof(f20,plain,(
% 15.86/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.86/2.50    inference(cnf_transformation,[],[f1])).
% 15.86/2.50  
% 15.86/2.50  fof(f8,axiom,(
% 15.86/2.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 15.86/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.50  
% 15.86/2.50  fof(f28,plain,(
% 15.86/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 15.86/2.50    inference(cnf_transformation,[],[f8])).
% 15.86/2.50  
% 15.86/2.50  fof(f2,axiom,(
% 15.86/2.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.86/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.50  
% 15.86/2.50  fof(f21,plain,(
% 15.86/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.86/2.50    inference(cnf_transformation,[],[f2])).
% 15.86/2.50  
% 15.86/2.50  fof(f11,axiom,(
% 15.86/2.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.86/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.50  
% 15.86/2.50  fof(f31,plain,(
% 15.86/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.86/2.50    inference(cnf_transformation,[],[f11])).
% 15.86/2.50  
% 15.86/2.50  fof(f34,plain,(
% 15.86/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 15.86/2.50    inference(definition_unfolding,[],[f21,f31,f31])).
% 15.86/2.50  
% 15.86/2.50  fof(f7,axiom,(
% 15.86/2.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 15.86/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.50  
% 15.86/2.50  fof(f27,plain,(
% 15.86/2.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.86/2.50    inference(cnf_transformation,[],[f7])).
% 15.86/2.50  
% 15.86/2.50  fof(f12,axiom,(
% 15.86/2.50    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 15.86/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.50  
% 15.86/2.50  fof(f32,plain,(
% 15.86/2.50    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 15.86/2.50    inference(cnf_transformation,[],[f12])).
% 15.86/2.50  
% 15.86/2.50  fof(f9,axiom,(
% 15.86/2.50    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 15.86/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.50  
% 15.86/2.50  fof(f29,plain,(
% 15.86/2.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 15.86/2.50    inference(cnf_transformation,[],[f9])).
% 15.86/2.50  
% 15.86/2.50  fof(f4,axiom,(
% 15.86/2.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 15.86/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.50  
% 15.86/2.50  fof(f17,plain,(
% 15.86/2.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 15.86/2.50    inference(nnf_transformation,[],[f4])).
% 15.86/2.50  
% 15.86/2.50  fof(f23,plain,(
% 15.86/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.86/2.50    inference(cnf_transformation,[],[f17])).
% 15.86/2.50  
% 15.86/2.50  fof(f5,axiom,(
% 15.86/2.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.86/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.50  
% 15.86/2.50  fof(f15,plain,(
% 15.86/2.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.86/2.50    inference(ennf_transformation,[],[f5])).
% 15.86/2.50  
% 15.86/2.50  fof(f25,plain,(
% 15.86/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.86/2.50    inference(cnf_transformation,[],[f15])).
% 15.86/2.50  
% 15.86/2.50  fof(f13,conjecture,(
% 15.86/2.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 15.86/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.50  
% 15.86/2.50  fof(f14,negated_conjecture,(
% 15.86/2.50    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 15.86/2.50    inference(negated_conjecture,[],[f13])).
% 15.86/2.50  
% 15.86/2.50  fof(f16,plain,(
% 15.86/2.50    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 15.86/2.50    inference(ennf_transformation,[],[f14])).
% 15.86/2.50  
% 15.86/2.50  fof(f18,plain,(
% 15.86/2.50    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 15.86/2.50    introduced(choice_axiom,[])).
% 15.86/2.50  
% 15.86/2.50  fof(f19,plain,(
% 15.86/2.50    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 15.86/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).
% 15.86/2.50  
% 15.86/2.50  fof(f33,plain,(
% 15.86/2.50    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 15.86/2.50    inference(cnf_transformation,[],[f19])).
% 15.86/2.50  
% 15.86/2.50  fof(f3,axiom,(
% 15.86/2.50    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 15.86/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.50  
% 15.86/2.50  fof(f22,plain,(
% 15.86/2.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 15.86/2.50    inference(cnf_transformation,[],[f3])).
% 15.86/2.50  
% 15.86/2.50  fof(f37,plain,(
% 15.86/2.50    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 15.86/2.50    inference(definition_unfolding,[],[f33,f31,f22,f22])).
% 15.86/2.50  
% 15.86/2.50  fof(f10,axiom,(
% 15.86/2.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.86/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.50  
% 15.86/2.50  fof(f30,plain,(
% 15.86/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.86/2.50    inference(cnf_transformation,[],[f10])).
% 15.86/2.50  
% 15.86/2.50  fof(f36,plain,(
% 15.86/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 15.86/2.50    inference(definition_unfolding,[],[f30,f31])).
% 15.86/2.50  
% 15.86/2.50  fof(f6,axiom,(
% 15.86/2.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 15.86/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.50  
% 15.86/2.50  fof(f26,plain,(
% 15.86/2.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 15.86/2.50    inference(cnf_transformation,[],[f6])).
% 15.86/2.50  
% 15.86/2.50  fof(f35,plain,(
% 15.86/2.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 15.86/2.50    inference(definition_unfolding,[],[f26,f31])).
% 15.86/2.50  
% 15.86/2.50  cnf(c_0,plain,
% 15.86/2.50      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 15.86/2.50      inference(cnf_transformation,[],[f20]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_7,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 15.86/2.50      inference(cnf_transformation,[],[f28]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_253,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_1,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 15.86/2.50      inference(cnf_transformation,[],[f34]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_950,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_253,c_1]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_6,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.86/2.50      inference(cnf_transformation,[],[f27]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_255,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_256,plain,
% 15.86/2.50      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.86/2.50      inference(light_normalisation,[status(thm)],[c_255,c_6]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_310,plain,
% 15.86/2.50      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_0,c_256]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_317,plain,
% 15.86/2.50      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_310,c_7]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_10,plain,
% 15.86/2.50      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.86/2.50      inference(cnf_transformation,[],[f32]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_320,plain,
% 15.86/2.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.86/2.50      inference(light_normalisation,[status(thm)],[c_317,c_10]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_8,plain,
% 15.86/2.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.86/2.50      inference(cnf_transformation,[],[f29]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_581,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_320,c_8]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_584,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_581,c_10]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_953,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 15.86/2.50      inference(light_normalisation,[status(thm)],[c_950,c_6,c_584]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_1835,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X0 ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_253,c_953]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_647,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_0,c_584]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_3,plain,
% 15.86/2.50      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.86/2.50      inference(cnf_transformation,[],[f23]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_50,plain,
% 15.86/2.50      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.86/2.50      inference(prop_impl,[status(thm)],[c_3]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_4,plain,
% 15.86/2.50      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 15.86/2.50      inference(cnf_transformation,[],[f25]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_88,plain,
% 15.86/2.50      ( k4_xboole_0(X0,X1) != k1_xboole_0 | k2_xboole_0(X0,X1) = X1 ),
% 15.86/2.50      inference(resolution,[status(thm)],[c_50,c_4]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_670,plain,
% 15.86/2.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_647,c_88]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_1318,plain,
% 15.86/2.50      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_0,c_670]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_1878,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 15.86/2.50      inference(light_normalisation,[status(thm)],[c_1835,c_1318]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_2668,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_1878,c_8]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_11,negated_conjecture,
% 15.86/2.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 15.86/2.50      inference(cnf_transformation,[],[f37]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_209,plain,
% 15.86/2.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_0,c_11]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_69783,plain,
% 15.86/2.50      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_2668,c_209]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_583,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_320,c_8]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_967,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_253,c_583]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_963,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_7,c_583]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_9,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 15.86/2.50      inference(cnf_transformation,[],[f36]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_485,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_4793,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_963,c_485]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_947,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_253,c_8]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_954,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_947,c_8]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_2647,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_647,c_1878]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_654,plain,
% 15.86/2.50      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_584,c_88]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_1223,plain,
% 15.86/2.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_0,c_654]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_2689,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 15.86/2.50      inference(light_normalisation,[status(thm)],[c_2647,c_1223]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_4798,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) = k4_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_4793,c_954,c_2689]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_5,plain,
% 15.86/2.50      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 15.86/2.50      inference(cnf_transformation,[],[f35]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_97,plain,
% 15.86/2.50      ( X0 != X1
% 15.86/2.50      | k4_xboole_0(X0,k4_xboole_0(X0,X2)) != X3
% 15.86/2.50      | k2_xboole_0(X3,X1) = X1 ),
% 15.86/2.50      inference(resolution_lifted,[status(thm)],[c_4,c_5]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_98,plain,
% 15.86/2.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
% 15.86/2.50      inference(unflattening,[status(thm)],[c_97]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_763,plain,
% 15.86/2.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) = X0 ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_1,c_98]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_785,plain,
% 15.86/2.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 15.86/2.50      inference(light_normalisation,[status(thm)],[c_763,c_485]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_801,plain,
% 15.86/2.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_785,c_7]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_806,plain,
% 15.86/2.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 15.86/2.50      inference(light_normalisation,[status(thm)],[c_801,c_320]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_891,plain,
% 15.86/2.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_806,c_8]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_898,plain,
% 15.86/2.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_891,c_8,c_10]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_1594,plain,
% 15.86/2.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_670,c_898]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_4799,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_4798,c_1594]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_458,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_17248,plain,
% 15.86/2.50      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k4_xboole_0(X0,X1)))),X2) = k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X1)),k2_xboole_0(k1_xboole_0,X2)) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_4799,c_458]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_17325,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 15.86/2.50      inference(light_normalisation,[status(thm)],[c_17248,c_963,c_2689]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_17326,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_17325,c_310]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_468,plain,
% 15.86/2.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_17282,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X1),k1_xboole_0) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_4799,c_468]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_3115,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_2689,c_8]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_3129,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_3115,c_310]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_13177,plain,
% 15.86/2.50      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X2,X3)) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_3129,c_8]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_17297,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X0),X0),X1) ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_17282,c_256,c_13177]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_17327,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X0),X0),X1) ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_17326,c_17297]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_17329,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X0) = k4_xboole_0(X1,X0) ),
% 15.86/2.50      inference(light_normalisation,[status(thm)],[c_17327,c_7,c_9]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_24827,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1))) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_17329,c_1]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_876,plain,
% 15.86/2.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_1,c_806]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_1539,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_876,c_8]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_24873,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X1,X0)) = X0 ),
% 15.86/2.50      inference(light_normalisation,[status(thm)],[c_24827,c_6,c_1539]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_30263,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1)),k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_967,c_24873]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_793,plain,
% 15.86/2.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_7,c_785]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_3611,plain,
% 15.86/2.50      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_670,c_793]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_3663,plain,
% 15.86/2.50      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 15.86/2.50      inference(light_normalisation,[status(thm)],[c_3611,c_647,c_1223]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_5052,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_967,c_485]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_5058,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.86/2.50      inference(light_normalisation,[status(thm)],[c_5052,c_2689,c_4799]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_31198,plain,
% 15.86/2.50      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 15.86/2.50      inference(light_normalisation,
% 15.86/2.50                [status(thm)],
% 15.86/2.50                [c_30263,c_3663,c_5058]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_31199,plain,
% 15.86/2.50      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_31198,c_2689]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_2132,plain,
% 15.86/2.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_670,c_1223]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_2141,plain,
% 15.86/2.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_1223,c_1223]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_2143,plain,
% 15.86/2.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_1223,c_670]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_2155,plain,
% 15.86/2.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_2143,c_1223]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_2157,plain,
% 15.86/2.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_2141,c_2155]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_2162,plain,
% 15.86/2.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_2132,c_2157]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_31958,plain,
% 15.86/2.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_31199,c_2162]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_32073,plain,
% 15.86/2.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 15.86/2.50      inference(light_normalisation,[status(thm)],[c_31958,c_2162]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_2145,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_1223,c_647]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_978,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_583,c_8]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_464,plain,
% 15.86/2.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_8,c_8]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_473,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_464,c_8]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_982,plain,
% 15.86/2.50      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X1)),X2)) = k1_xboole_0 ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_978,c_10,c_473]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_5434,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0),X2)) = k1_xboole_0 ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_2145,c_982]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_3726,plain,
% 15.86/2.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_3663,c_2157]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_804,plain,
% 15.86/2.50      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_785,c_0]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_858,plain,
% 15.86/2.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_1,c_804]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_1360,plain,
% 15.86/2.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,X1) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_584,c_858]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_1379,plain,
% 15.86/2.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 15.86/2.50      inference(light_normalisation,[status(thm)],[c_1360,c_6]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_2895,plain,
% 15.86/2.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),X0) ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_2157,c_1379]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_2923,plain,
% 15.86/2.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_2895,c_2157]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_3763,plain,
% 15.86/2.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 15.86/2.50      inference(light_normalisation,[status(thm)],[c_3726,c_2923]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_5486,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_5434,c_473,c_3763]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_18147,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_785,c_5486]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_36202,plain,
% 15.86/2.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.86/2.50      inference(superposition,[status(thm)],[c_32073,c_18147]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_69784,plain,
% 15.86/2.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 15.86/2.50      inference(demodulation,[status(thm)],[c_69783,c_256,c_36202]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(c_345,plain,
% 15.86/2.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 15.86/2.50      inference(instantiation,[status(thm)],[c_1]) ).
% 15.86/2.50  
% 15.86/2.50  cnf(contradiction,plain,
% 15.86/2.50      ( $false ),
% 15.86/2.50      inference(minisat,[status(thm)],[c_69784,c_345]) ).
% 15.86/2.50  
% 15.86/2.50  
% 15.86/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.86/2.50  
% 15.86/2.50  ------                               Statistics
% 15.86/2.50  
% 15.86/2.50  ------ General
% 15.86/2.50  
% 15.86/2.50  abstr_ref_over_cycles:                  0
% 15.86/2.50  abstr_ref_under_cycles:                 0
% 15.86/2.50  gc_basic_clause_elim:                   0
% 15.86/2.50  forced_gc_time:                         0
% 15.86/2.50  parsing_time:                           0.008
% 15.86/2.50  unif_index_cands_time:                  0.
% 15.86/2.50  unif_index_add_time:                    0.
% 15.86/2.50  orderings_time:                         0.
% 15.86/2.50  out_proof_time:                         0.008
% 15.86/2.50  total_time:                             1.854
% 15.86/2.50  num_of_symbols:                         41
% 15.86/2.50  num_of_terms:                           96715
% 15.86/2.50  
% 15.86/2.50  ------ Preprocessing
% 15.86/2.50  
% 15.86/2.50  num_of_splits:                          0
% 15.86/2.50  num_of_split_atoms:                     4
% 15.86/2.50  num_of_reused_defs:                     2
% 15.86/2.50  num_eq_ax_congr_red:                    1
% 15.86/2.50  num_of_sem_filtered_clauses:            0
% 15.86/2.50  num_of_subtypes:                        0
% 15.86/2.50  monotx_restored_types:                  0
% 15.86/2.50  sat_num_of_epr_types:                   0
% 15.86/2.50  sat_num_of_non_cyclic_types:            0
% 15.86/2.50  sat_guarded_non_collapsed_types:        0
% 15.86/2.50  num_pure_diseq_elim:                    0
% 15.86/2.50  simp_replaced_by:                       0
% 15.86/2.50  res_preprocessed:                       38
% 15.86/2.50  prep_upred:                             0
% 15.86/2.50  prep_unflattend:                        4
% 15.86/2.50  smt_new_axioms:                         0
% 15.86/2.50  pred_elim_cands:                        0
% 15.86/2.50  pred_elim:                              1
% 15.86/2.50  pred_elim_cl:                           1
% 15.86/2.50  pred_elim_cycles:                       2
% 15.86/2.50  merged_defs:                            2
% 15.86/2.50  merged_defs_ncl:                        0
% 15.86/2.50  bin_hyper_res:                          2
% 15.86/2.50  prep_cycles:                            3
% 15.86/2.50  pred_elim_time:                         0.
% 15.86/2.50  splitting_time:                         0.
% 15.86/2.50  sem_filter_time:                        0.
% 15.86/2.50  monotx_time:                            0.
% 15.86/2.50  subtype_inf_time:                       0.
% 15.86/2.50  
% 15.86/2.50  ------ Problem properties
% 15.86/2.50  
% 15.86/2.50  clauses:                                11
% 15.86/2.50  conjectures:                            1
% 15.86/2.50  epr:                                    0
% 15.86/2.50  horn:                                   11
% 15.86/2.50  ground:                                 1
% 15.86/2.50  unary:                                  10
% 15.86/2.50  binary:                                 1
% 15.86/2.50  lits:                                   12
% 15.86/2.50  lits_eq:                                12
% 15.86/2.50  fd_pure:                                0
% 15.86/2.50  fd_pseudo:                              0
% 15.86/2.50  fd_cond:                                0
% 15.86/2.50  fd_pseudo_cond:                         0
% 15.86/2.50  ac_symbols:                             1
% 15.86/2.50  
% 15.86/2.50  ------ Propositional Solver
% 15.86/2.50  
% 15.86/2.50  prop_solver_calls:                      32
% 15.86/2.50  prop_fast_solver_calls:                 408
% 15.86/2.50  smt_solver_calls:                       0
% 15.86/2.50  smt_fast_solver_calls:                  0
% 15.86/2.50  prop_num_of_clauses:                    12033
% 15.86/2.50  prop_preprocess_simplified:             13734
% 15.86/2.50  prop_fo_subsumed:                       0
% 15.86/2.50  prop_solver_time:                       0.
% 15.86/2.50  smt_solver_time:                        0.
% 15.86/2.50  smt_fast_solver_time:                   0.
% 15.86/2.50  prop_fast_solver_time:                  0.
% 15.86/2.50  prop_unsat_core_time:                   0.001
% 15.86/2.50  
% 15.86/2.50  ------ QBF
% 15.86/2.50  
% 15.86/2.50  qbf_q_res:                              0
% 15.86/2.50  qbf_num_tautologies:                    0
% 15.86/2.50  qbf_prep_cycles:                        0
% 15.86/2.50  
% 15.86/2.50  ------ BMC1
% 15.86/2.50  
% 15.86/2.50  bmc1_current_bound:                     -1
% 15.86/2.50  bmc1_last_solved_bound:                 -1
% 15.86/2.50  bmc1_unsat_core_size:                   -1
% 15.86/2.50  bmc1_unsat_core_parents_size:           -1
% 15.86/2.50  bmc1_merge_next_fun:                    0
% 15.86/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.86/2.50  
% 15.86/2.50  ------ Instantiation
% 15.86/2.50  
% 15.86/2.50  inst_num_of_clauses:                    3288
% 15.86/2.50  inst_num_in_passive:                    1728
% 15.86/2.50  inst_num_in_active:                     1036
% 15.86/2.50  inst_num_in_unprocessed:                524
% 15.86/2.50  inst_num_of_loops:                      1100
% 15.86/2.50  inst_num_of_learning_restarts:          0
% 15.86/2.50  inst_num_moves_active_passive:          58
% 15.86/2.50  inst_lit_activity:                      0
% 15.86/2.50  inst_lit_activity_moves:                1
% 15.86/2.50  inst_num_tautologies:                   0
% 15.86/2.50  inst_num_prop_implied:                  0
% 15.86/2.50  inst_num_existing_simplified:           0
% 15.86/2.50  inst_num_eq_res_simplified:             0
% 15.86/2.50  inst_num_child_elim:                    0
% 15.86/2.50  inst_num_of_dismatching_blockings:      2308
% 15.86/2.50  inst_num_of_non_proper_insts:           6176
% 15.86/2.50  inst_num_of_duplicates:                 0
% 15.86/2.50  inst_inst_num_from_inst_to_res:         0
% 15.86/2.50  inst_dismatching_checking_time:         0.
% 15.86/2.50  
% 15.86/2.50  ------ Resolution
% 15.86/2.50  
% 15.86/2.50  res_num_of_clauses:                     0
% 15.86/2.50  res_num_in_passive:                     0
% 15.86/2.50  res_num_in_active:                      0
% 15.86/2.50  res_num_of_loops:                       41
% 15.86/2.50  res_forward_subset_subsumed:            1208
% 15.86/2.50  res_backward_subset_subsumed:           8
% 15.86/2.50  res_forward_subsumed:                   0
% 15.86/2.50  res_backward_subsumed:                  0
% 15.86/2.50  res_forward_subsumption_resolution:     0
% 15.86/2.50  res_backward_subsumption_resolution:    0
% 15.86/2.50  res_clause_to_clause_subsumption:       111194
% 15.86/2.50  res_orphan_elimination:                 0
% 15.86/2.50  res_tautology_del:                      1086
% 15.86/2.50  res_num_eq_res_simplified:              0
% 15.86/2.50  res_num_sel_changes:                    0
% 15.86/2.50  res_moves_from_active_to_pass:          0
% 15.86/2.50  
% 15.86/2.50  ------ Superposition
% 15.86/2.50  
% 15.86/2.50  sup_time_total:                         0.
% 15.86/2.50  sup_time_generating:                    0.
% 15.86/2.50  sup_time_sim_full:                      0.
% 15.86/2.50  sup_time_sim_immed:                     0.
% 15.86/2.50  
% 15.86/2.50  sup_num_of_clauses:                     4399
% 15.86/2.50  sup_num_in_active:                      140
% 15.86/2.50  sup_num_in_passive:                     4259
% 15.86/2.50  sup_num_of_loops:                       218
% 15.86/2.50  sup_fw_superposition:                   18671
% 15.86/2.50  sup_bw_superposition:                   15110
% 15.86/2.50  sup_immediate_simplified:               16678
% 15.86/2.50  sup_given_eliminated:                   7
% 15.86/2.50  comparisons_done:                       0
% 15.86/2.50  comparisons_avoided:                    0
% 15.86/2.50  
% 15.86/2.50  ------ Simplifications
% 15.86/2.50  
% 15.86/2.50  
% 15.86/2.50  sim_fw_subset_subsumed:                 5
% 15.86/2.50  sim_bw_subset_subsumed:                 0
% 15.86/2.50  sim_fw_subsumed:                        2642
% 15.86/2.50  sim_bw_subsumed:                        50
% 15.86/2.50  sim_fw_subsumption_res:                 0
% 15.86/2.50  sim_bw_subsumption_res:                 0
% 15.86/2.50  sim_tautology_del:                      29
% 15.86/2.50  sim_eq_tautology_del:                   5365
% 15.86/2.50  sim_eq_res_simp:                        8
% 15.86/2.50  sim_fw_demodulated:                     10708
% 15.86/2.50  sim_bw_demodulated:                     165
% 15.86/2.50  sim_light_normalised:                   6481
% 15.86/2.50  sim_joinable_taut:                      60
% 15.86/2.50  sim_joinable_simp:                      0
% 15.86/2.50  sim_ac_normalised:                      0
% 15.86/2.50  sim_smt_subsumption:                    0
% 15.86/2.50  
%------------------------------------------------------------------------------
