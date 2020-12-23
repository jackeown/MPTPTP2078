%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:04 EST 2020

% Result     : Theorem 51.60s
% Output     : CNFRefutation 51.60s
% Verified   : 
% Statistics : Number of formulae       :  131 (2109 expanded)
%              Number of clauses        :   91 ( 833 expanded)
%              Number of leaves         :   15 ( 540 expanded)
%              Depth                    :   23
%              Number of atoms          :  139 (2474 expanded)
%              Number of equality atoms :  130 (2057 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   3 average)

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

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f31,f31])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f32,f31,f31])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f14,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f18,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f19,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f34,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f40,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f34,f31,f23,f23])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_65,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_7])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_136,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_65,c_8])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_48,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k4_xboole_0(X3,X1) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_6])).

cnf(c_49,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_48])).

cnf(c_83,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_49,c_7])).

cnf(c_155,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_136,c_83])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_183,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_7,c_3])).

cnf(c_216,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_183,c_7,c_65])).

cnf(c_366,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_216])).

cnf(c_1034,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_155,c_366])).

cnf(c_1059,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1034,c_7])).

cnf(c_1669,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_1059])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_66,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_9,c_8])).

cnf(c_118,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_1,c_66])).

cnf(c_119,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_118,c_8])).

cnf(c_177,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7,c_3])).

cnf(c_221,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_177,c_7,c_83])).

cnf(c_147,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_49])).

cnf(c_10,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_330,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_147,c_10])).

cnf(c_338,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_330,c_7,c_216])).

cnf(c_825,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_221,c_338])).

cnf(c_7289,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X0)),X1)) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_119,c_825])).

cnf(c_7428,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_7289,c_147])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_69,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_7429,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_7428,c_69])).

cnf(c_8495,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_1669,c_7429])).

cnf(c_8623,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_8495,c_7429])).

cnf(c_8956,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0)))) = k4_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_8623,c_119])).

cnf(c_328,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_147,c_8])).

cnf(c_137,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_8,c_8])).

cnf(c_154,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_137,c_8])).

cnf(c_339,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_328,c_83,c_154])).

cnf(c_863,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_339])).

cnf(c_8973,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_8956,c_863])).

cnf(c_8974,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_8973,c_4,c_8])).

cnf(c_11,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_68,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_11])).

cnf(c_139324,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_8974,c_68])).

cnf(c_8542,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7429,c_1])).

cnf(c_8595,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_8542,c_7,c_155])).

cnf(c_256,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_65,c_10])).

cnf(c_261,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_256,c_7,c_216])).

cnf(c_428,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_261,c_261])).

cnf(c_1195,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_428,c_3])).

cnf(c_1206,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_1195,c_8])).

cnf(c_148,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_65])).

cnf(c_1207,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X2)) = X0 ),
    inference(demodulation,[status(thm)],[c_1206,c_7,c_148])).

cnf(c_8763,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8595,c_1207])).

cnf(c_8784,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_8763,c_7429])).

cnf(c_135,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_49,c_8])).

cnf(c_156,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_135,c_8,c_83])).

cnf(c_755,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_156])).

cnf(c_8704,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_755,c_8595])).

cnf(c_394,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_221])).

cnf(c_1107,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k1_xboole_0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_156,c_394])).

cnf(c_1138,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X2,k1_xboole_0))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1107,c_8])).

cnf(c_1139,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1138,c_4])).

cnf(c_8021,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1139])).

cnf(c_8813,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_8704,c_8021])).

cnf(c_9373,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8784,c_8813])).

cnf(c_9507,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_9373,c_8813])).

cnf(c_431,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_261,c_3])).

cnf(c_442,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_431,c_7,c_65])).

cnf(c_4776,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_442])).

cnf(c_1101,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_147,c_394])).

cnf(c_1146,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1101,c_7])).

cnf(c_1777,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1146])).

cnf(c_1827,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1669,c_339])).

cnf(c_16964,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X1,X0)),X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1777,c_1827])).

cnf(c_1027,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_147,c_366])).

cnf(c_1068,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1027,c_7])).

cnf(c_1697,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1068])).

cnf(c_1282,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[status(thm)],[c_755,c_8])).

cnf(c_1309,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),X3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1282,c_8,c_83])).

cnf(c_10639,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,k2_xboole_0(X1,X0)),X3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8813,c_1309])).

cnf(c_17212,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16964,c_154,c_1697,c_10639])).

cnf(c_33218,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4776,c_17212])).

cnf(c_37434,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9507,c_33218])).

cnf(c_139325,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_139324,c_4,c_37434])).

cnf(c_140379,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1,c_139325])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:52:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 51.60/7.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.60/7.00  
% 51.60/7.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.60/7.00  
% 51.60/7.00  ------  iProver source info
% 51.60/7.00  
% 51.60/7.00  git: date: 2020-06-30 10:37:57 +0100
% 51.60/7.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.60/7.00  git: non_committed_changes: false
% 51.60/7.00  git: last_make_outside_of_git: false
% 51.60/7.00  
% 51.60/7.00  ------ 
% 51.60/7.00  
% 51.60/7.00  ------ Input Options
% 51.60/7.00  
% 51.60/7.00  --out_options                           all
% 51.60/7.00  --tptp_safe_out                         true
% 51.60/7.00  --problem_path                          ""
% 51.60/7.00  --include_path                          ""
% 51.60/7.00  --clausifier                            res/vclausify_rel
% 51.60/7.00  --clausifier_options                    ""
% 51.60/7.00  --stdin                                 false
% 51.60/7.00  --stats_out                             all
% 51.60/7.00  
% 51.60/7.00  ------ General Options
% 51.60/7.00  
% 51.60/7.00  --fof                                   false
% 51.60/7.00  --time_out_real                         305.
% 51.60/7.00  --time_out_virtual                      -1.
% 51.60/7.00  --symbol_type_check                     false
% 51.60/7.00  --clausify_out                          false
% 51.60/7.00  --sig_cnt_out                           false
% 51.60/7.00  --trig_cnt_out                          false
% 51.60/7.00  --trig_cnt_out_tolerance                1.
% 51.60/7.00  --trig_cnt_out_sk_spl                   false
% 51.60/7.00  --abstr_cl_out                          false
% 51.60/7.00  
% 51.60/7.00  ------ Global Options
% 51.60/7.00  
% 51.60/7.00  --schedule                              default
% 51.60/7.00  --add_important_lit                     false
% 51.60/7.00  --prop_solver_per_cl                    1000
% 51.60/7.00  --min_unsat_core                        false
% 51.60/7.00  --soft_assumptions                      false
% 51.60/7.00  --soft_lemma_size                       3
% 51.60/7.00  --prop_impl_unit_size                   0
% 51.60/7.00  --prop_impl_unit                        []
% 51.60/7.00  --share_sel_clauses                     true
% 51.60/7.00  --reset_solvers                         false
% 51.60/7.00  --bc_imp_inh                            [conj_cone]
% 51.60/7.00  --conj_cone_tolerance                   3.
% 51.60/7.00  --extra_neg_conj                        none
% 51.60/7.00  --large_theory_mode                     true
% 51.60/7.00  --prolific_symb_bound                   200
% 51.60/7.00  --lt_threshold                          2000
% 51.60/7.00  --clause_weak_htbl                      true
% 51.60/7.00  --gc_record_bc_elim                     false
% 51.60/7.00  
% 51.60/7.00  ------ Preprocessing Options
% 51.60/7.00  
% 51.60/7.00  --preprocessing_flag                    true
% 51.60/7.00  --time_out_prep_mult                    0.1
% 51.60/7.00  --splitting_mode                        input
% 51.60/7.00  --splitting_grd                         true
% 51.60/7.00  --splitting_cvd                         false
% 51.60/7.00  --splitting_cvd_svl                     false
% 51.60/7.00  --splitting_nvd                         32
% 51.60/7.00  --sub_typing                            true
% 51.60/7.00  --prep_gs_sim                           true
% 51.60/7.00  --prep_unflatten                        true
% 51.60/7.00  --prep_res_sim                          true
% 51.60/7.00  --prep_upred                            true
% 51.60/7.00  --prep_sem_filter                       exhaustive
% 51.60/7.00  --prep_sem_filter_out                   false
% 51.60/7.00  --pred_elim                             true
% 51.60/7.00  --res_sim_input                         true
% 51.60/7.00  --eq_ax_congr_red                       true
% 51.60/7.00  --pure_diseq_elim                       true
% 51.60/7.00  --brand_transform                       false
% 51.60/7.00  --non_eq_to_eq                          false
% 51.60/7.00  --prep_def_merge                        true
% 51.60/7.00  --prep_def_merge_prop_impl              false
% 51.60/7.00  --prep_def_merge_mbd                    true
% 51.60/7.00  --prep_def_merge_tr_red                 false
% 51.60/7.00  --prep_def_merge_tr_cl                  false
% 51.60/7.00  --smt_preprocessing                     true
% 51.60/7.00  --smt_ac_axioms                         fast
% 51.60/7.00  --preprocessed_out                      false
% 51.60/7.00  --preprocessed_stats                    false
% 51.60/7.00  
% 51.60/7.00  ------ Abstraction refinement Options
% 51.60/7.00  
% 51.60/7.00  --abstr_ref                             []
% 51.60/7.00  --abstr_ref_prep                        false
% 51.60/7.00  --abstr_ref_until_sat                   false
% 51.60/7.00  --abstr_ref_sig_restrict                funpre
% 51.60/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.60/7.00  --abstr_ref_under                       []
% 51.60/7.00  
% 51.60/7.00  ------ SAT Options
% 51.60/7.00  
% 51.60/7.00  --sat_mode                              false
% 51.60/7.00  --sat_fm_restart_options                ""
% 51.60/7.00  --sat_gr_def                            false
% 51.60/7.00  --sat_epr_types                         true
% 51.60/7.00  --sat_non_cyclic_types                  false
% 51.60/7.00  --sat_finite_models                     false
% 51.60/7.00  --sat_fm_lemmas                         false
% 51.60/7.00  --sat_fm_prep                           false
% 51.60/7.00  --sat_fm_uc_incr                        true
% 51.60/7.00  --sat_out_model                         small
% 51.60/7.00  --sat_out_clauses                       false
% 51.60/7.00  
% 51.60/7.00  ------ QBF Options
% 51.60/7.00  
% 51.60/7.00  --qbf_mode                              false
% 51.60/7.00  --qbf_elim_univ                         false
% 51.60/7.00  --qbf_dom_inst                          none
% 51.60/7.00  --qbf_dom_pre_inst                      false
% 51.60/7.00  --qbf_sk_in                             false
% 51.60/7.00  --qbf_pred_elim                         true
% 51.60/7.00  --qbf_split                             512
% 51.60/7.00  
% 51.60/7.00  ------ BMC1 Options
% 51.60/7.00  
% 51.60/7.00  --bmc1_incremental                      false
% 51.60/7.00  --bmc1_axioms                           reachable_all
% 51.60/7.00  --bmc1_min_bound                        0
% 51.60/7.00  --bmc1_max_bound                        -1
% 51.60/7.00  --bmc1_max_bound_default                -1
% 51.60/7.00  --bmc1_symbol_reachability              true
% 51.60/7.00  --bmc1_property_lemmas                  false
% 51.60/7.00  --bmc1_k_induction                      false
% 51.60/7.00  --bmc1_non_equiv_states                 false
% 51.60/7.00  --bmc1_deadlock                         false
% 51.60/7.00  --bmc1_ucm                              false
% 51.60/7.00  --bmc1_add_unsat_core                   none
% 51.60/7.00  --bmc1_unsat_core_children              false
% 51.60/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.60/7.00  --bmc1_out_stat                         full
% 51.60/7.00  --bmc1_ground_init                      false
% 51.60/7.00  --bmc1_pre_inst_next_state              false
% 51.60/7.00  --bmc1_pre_inst_state                   false
% 51.60/7.00  --bmc1_pre_inst_reach_state             false
% 51.60/7.00  --bmc1_out_unsat_core                   false
% 51.60/7.00  --bmc1_aig_witness_out                  false
% 51.60/7.00  --bmc1_verbose                          false
% 51.60/7.00  --bmc1_dump_clauses_tptp                false
% 51.60/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.60/7.00  --bmc1_dump_file                        -
% 51.60/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.60/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.60/7.00  --bmc1_ucm_extend_mode                  1
% 51.60/7.00  --bmc1_ucm_init_mode                    2
% 51.60/7.00  --bmc1_ucm_cone_mode                    none
% 51.60/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.60/7.00  --bmc1_ucm_relax_model                  4
% 51.60/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.60/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.60/7.00  --bmc1_ucm_layered_model                none
% 51.60/7.00  --bmc1_ucm_max_lemma_size               10
% 51.60/7.00  
% 51.60/7.00  ------ AIG Options
% 51.60/7.00  
% 51.60/7.00  --aig_mode                              false
% 51.60/7.00  
% 51.60/7.00  ------ Instantiation Options
% 51.60/7.00  
% 51.60/7.00  --instantiation_flag                    true
% 51.60/7.00  --inst_sos_flag                         true
% 51.60/7.00  --inst_sos_phase                        true
% 51.60/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.60/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.60/7.00  --inst_lit_sel_side                     num_symb
% 51.60/7.00  --inst_solver_per_active                1400
% 51.60/7.00  --inst_solver_calls_frac                1.
% 51.60/7.00  --inst_passive_queue_type               priority_queues
% 51.60/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.60/7.00  --inst_passive_queues_freq              [25;2]
% 51.60/7.00  --inst_dismatching                      true
% 51.60/7.00  --inst_eager_unprocessed_to_passive     true
% 51.60/7.00  --inst_prop_sim_given                   true
% 51.60/7.00  --inst_prop_sim_new                     false
% 51.60/7.00  --inst_subs_new                         false
% 51.60/7.00  --inst_eq_res_simp                      false
% 51.60/7.00  --inst_subs_given                       false
% 51.60/7.00  --inst_orphan_elimination               true
% 51.60/7.00  --inst_learning_loop_flag               true
% 51.60/7.00  --inst_learning_start                   3000
% 51.60/7.00  --inst_learning_factor                  2
% 51.60/7.00  --inst_start_prop_sim_after_learn       3
% 51.60/7.00  --inst_sel_renew                        solver
% 51.60/7.00  --inst_lit_activity_flag                true
% 51.60/7.00  --inst_restr_to_given                   false
% 51.60/7.00  --inst_activity_threshold               500
% 51.60/7.00  --inst_out_proof                        true
% 51.60/7.00  
% 51.60/7.00  ------ Resolution Options
% 51.60/7.00  
% 51.60/7.00  --resolution_flag                       true
% 51.60/7.00  --res_lit_sel                           adaptive
% 51.60/7.00  --res_lit_sel_side                      none
% 51.60/7.00  --res_ordering                          kbo
% 51.60/7.00  --res_to_prop_solver                    active
% 51.60/7.00  --res_prop_simpl_new                    false
% 51.60/7.00  --res_prop_simpl_given                  true
% 51.60/7.00  --res_passive_queue_type                priority_queues
% 51.60/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.60/7.00  --res_passive_queues_freq               [15;5]
% 51.60/7.00  --res_forward_subs                      full
% 51.60/7.00  --res_backward_subs                     full
% 51.60/7.00  --res_forward_subs_resolution           true
% 51.60/7.00  --res_backward_subs_resolution          true
% 51.60/7.00  --res_orphan_elimination                true
% 51.60/7.00  --res_time_limit                        2.
% 51.60/7.00  --res_out_proof                         true
% 51.60/7.00  
% 51.60/7.00  ------ Superposition Options
% 51.60/7.00  
% 51.60/7.00  --superposition_flag                    true
% 51.60/7.00  --sup_passive_queue_type                priority_queues
% 51.60/7.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.60/7.00  --sup_passive_queues_freq               [8;1;4]
% 51.60/7.00  --demod_completeness_check              fast
% 51.60/7.00  --demod_use_ground                      true
% 51.60/7.00  --sup_to_prop_solver                    passive
% 51.60/7.00  --sup_prop_simpl_new                    true
% 51.60/7.00  --sup_prop_simpl_given                  true
% 51.60/7.00  --sup_fun_splitting                     true
% 51.60/7.00  --sup_smt_interval                      50000
% 51.60/7.00  
% 51.60/7.00  ------ Superposition Simplification Setup
% 51.60/7.00  
% 51.60/7.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.60/7.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.60/7.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.60/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.60/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 51.60/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.60/7.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.60/7.00  --sup_immed_triv                        [TrivRules]
% 51.60/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.60/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.60/7.00  --sup_immed_bw_main                     []
% 51.60/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.60/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.60/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.60/7.00  --sup_input_bw                          []
% 51.60/7.00  
% 51.60/7.00  ------ Combination Options
% 51.60/7.00  
% 51.60/7.00  --comb_res_mult                         3
% 51.60/7.00  --comb_sup_mult                         2
% 51.60/7.00  --comb_inst_mult                        10
% 51.60/7.00  
% 51.60/7.00  ------ Debug Options
% 51.60/7.00  
% 51.60/7.00  --dbg_backtrace                         false
% 51.60/7.00  --dbg_dump_prop_clauses                 false
% 51.60/7.00  --dbg_dump_prop_clauses_file            -
% 51.60/7.00  --dbg_out_stat                          false
% 51.60/7.00  ------ Parsing...
% 51.60/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.60/7.00  
% 51.60/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 51.60/7.00  
% 51.60/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.60/7.00  
% 51.60/7.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 51.60/7.00  ------ Proving...
% 51.60/7.00  ------ Problem Properties 
% 51.60/7.00  
% 51.60/7.00  
% 51.60/7.00  clauses                                 11
% 51.60/7.00  conjectures                             1
% 51.60/7.00  EPR                                     0
% 51.60/7.00  Horn                                    11
% 51.60/7.00  unary                                   11
% 51.60/7.00  binary                                  0
% 51.60/7.00  lits                                    11
% 51.60/7.00  lits eq                                 11
% 51.60/7.00  fd_pure                                 0
% 51.60/7.00  fd_pseudo                               0
% 51.60/7.00  fd_cond                                 0
% 51.60/7.00  fd_pseudo_cond                          0
% 51.60/7.00  AC symbols                              0
% 51.60/7.00  
% 51.60/7.00  ------ Schedule UEQ
% 51.60/7.00  
% 51.60/7.00  ------ pure equality problem: resolution off 
% 51.60/7.00  
% 51.60/7.00  ------ Option_UEQ Time Limit: Unbounded
% 51.60/7.00  
% 51.60/7.00  
% 51.60/7.00  ------ 
% 51.60/7.00  Current options:
% 51.60/7.00  ------ 
% 51.60/7.00  
% 51.60/7.00  ------ Input Options
% 51.60/7.00  
% 51.60/7.00  --out_options                           all
% 51.60/7.00  --tptp_safe_out                         true
% 51.60/7.00  --problem_path                          ""
% 51.60/7.00  --include_path                          ""
% 51.60/7.00  --clausifier                            res/vclausify_rel
% 51.60/7.00  --clausifier_options                    ""
% 51.60/7.00  --stdin                                 false
% 51.60/7.00  --stats_out                             all
% 51.60/7.00  
% 51.60/7.00  ------ General Options
% 51.60/7.00  
% 51.60/7.00  --fof                                   false
% 51.60/7.00  --time_out_real                         305.
% 51.60/7.00  --time_out_virtual                      -1.
% 51.60/7.00  --symbol_type_check                     false
% 51.60/7.00  --clausify_out                          false
% 51.60/7.00  --sig_cnt_out                           false
% 51.60/7.00  --trig_cnt_out                          false
% 51.60/7.00  --trig_cnt_out_tolerance                1.
% 51.60/7.00  --trig_cnt_out_sk_spl                   false
% 51.60/7.00  --abstr_cl_out                          false
% 51.60/7.00  
% 51.60/7.00  ------ Global Options
% 51.60/7.00  
% 51.60/7.00  --schedule                              default
% 51.60/7.00  --add_important_lit                     false
% 51.60/7.00  --prop_solver_per_cl                    1000
% 51.60/7.00  --min_unsat_core                        false
% 51.60/7.00  --soft_assumptions                      false
% 51.60/7.00  --soft_lemma_size                       3
% 51.60/7.00  --prop_impl_unit_size                   0
% 51.60/7.00  --prop_impl_unit                        []
% 51.60/7.00  --share_sel_clauses                     true
% 51.60/7.00  --reset_solvers                         false
% 51.60/7.00  --bc_imp_inh                            [conj_cone]
% 51.60/7.00  --conj_cone_tolerance                   3.
% 51.60/7.00  --extra_neg_conj                        none
% 51.60/7.00  --large_theory_mode                     true
% 51.60/7.00  --prolific_symb_bound                   200
% 51.60/7.00  --lt_threshold                          2000
% 51.60/7.00  --clause_weak_htbl                      true
% 51.60/7.00  --gc_record_bc_elim                     false
% 51.60/7.00  
% 51.60/7.00  ------ Preprocessing Options
% 51.60/7.00  
% 51.60/7.00  --preprocessing_flag                    true
% 51.60/7.00  --time_out_prep_mult                    0.1
% 51.60/7.00  --splitting_mode                        input
% 51.60/7.00  --splitting_grd                         true
% 51.60/7.00  --splitting_cvd                         false
% 51.60/7.00  --splitting_cvd_svl                     false
% 51.60/7.00  --splitting_nvd                         32
% 51.60/7.00  --sub_typing                            true
% 51.60/7.00  --prep_gs_sim                           true
% 51.60/7.00  --prep_unflatten                        true
% 51.60/7.00  --prep_res_sim                          true
% 51.60/7.00  --prep_upred                            true
% 51.60/7.00  --prep_sem_filter                       exhaustive
% 51.60/7.00  --prep_sem_filter_out                   false
% 51.60/7.00  --pred_elim                             true
% 51.60/7.00  --res_sim_input                         true
% 51.60/7.00  --eq_ax_congr_red                       true
% 51.60/7.00  --pure_diseq_elim                       true
% 51.60/7.00  --brand_transform                       false
% 51.60/7.00  --non_eq_to_eq                          false
% 51.60/7.00  --prep_def_merge                        true
% 51.60/7.00  --prep_def_merge_prop_impl              false
% 51.60/7.00  --prep_def_merge_mbd                    true
% 51.60/7.00  --prep_def_merge_tr_red                 false
% 51.60/7.00  --prep_def_merge_tr_cl                  false
% 51.60/7.00  --smt_preprocessing                     true
% 51.60/7.00  --smt_ac_axioms                         fast
% 51.60/7.00  --preprocessed_out                      false
% 51.60/7.00  --preprocessed_stats                    false
% 51.60/7.00  
% 51.60/7.00  ------ Abstraction refinement Options
% 51.60/7.00  
% 51.60/7.00  --abstr_ref                             []
% 51.60/7.00  --abstr_ref_prep                        false
% 51.60/7.00  --abstr_ref_until_sat                   false
% 51.60/7.00  --abstr_ref_sig_restrict                funpre
% 51.60/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.60/7.00  --abstr_ref_under                       []
% 51.60/7.00  
% 51.60/7.00  ------ SAT Options
% 51.60/7.00  
% 51.60/7.00  --sat_mode                              false
% 51.60/7.00  --sat_fm_restart_options                ""
% 51.60/7.00  --sat_gr_def                            false
% 51.60/7.00  --sat_epr_types                         true
% 51.60/7.00  --sat_non_cyclic_types                  false
% 51.60/7.00  --sat_finite_models                     false
% 51.60/7.00  --sat_fm_lemmas                         false
% 51.60/7.00  --sat_fm_prep                           false
% 51.60/7.00  --sat_fm_uc_incr                        true
% 51.60/7.00  --sat_out_model                         small
% 51.60/7.00  --sat_out_clauses                       false
% 51.60/7.00  
% 51.60/7.00  ------ QBF Options
% 51.60/7.00  
% 51.60/7.00  --qbf_mode                              false
% 51.60/7.00  --qbf_elim_univ                         false
% 51.60/7.00  --qbf_dom_inst                          none
% 51.60/7.00  --qbf_dom_pre_inst                      false
% 51.60/7.00  --qbf_sk_in                             false
% 51.60/7.00  --qbf_pred_elim                         true
% 51.60/7.00  --qbf_split                             512
% 51.60/7.00  
% 51.60/7.00  ------ BMC1 Options
% 51.60/7.00  
% 51.60/7.00  --bmc1_incremental                      false
% 51.60/7.00  --bmc1_axioms                           reachable_all
% 51.60/7.00  --bmc1_min_bound                        0
% 51.60/7.00  --bmc1_max_bound                        -1
% 51.60/7.00  --bmc1_max_bound_default                -1
% 51.60/7.00  --bmc1_symbol_reachability              true
% 51.60/7.00  --bmc1_property_lemmas                  false
% 51.60/7.00  --bmc1_k_induction                      false
% 51.60/7.00  --bmc1_non_equiv_states                 false
% 51.60/7.00  --bmc1_deadlock                         false
% 51.60/7.00  --bmc1_ucm                              false
% 51.60/7.00  --bmc1_add_unsat_core                   none
% 51.60/7.00  --bmc1_unsat_core_children              false
% 51.60/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.60/7.00  --bmc1_out_stat                         full
% 51.60/7.00  --bmc1_ground_init                      false
% 51.60/7.00  --bmc1_pre_inst_next_state              false
% 51.60/7.00  --bmc1_pre_inst_state                   false
% 51.60/7.00  --bmc1_pre_inst_reach_state             false
% 51.60/7.00  --bmc1_out_unsat_core                   false
% 51.60/7.00  --bmc1_aig_witness_out                  false
% 51.60/7.00  --bmc1_verbose                          false
% 51.60/7.00  --bmc1_dump_clauses_tptp                false
% 51.60/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.60/7.00  --bmc1_dump_file                        -
% 51.60/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.60/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.60/7.00  --bmc1_ucm_extend_mode                  1
% 51.60/7.00  --bmc1_ucm_init_mode                    2
% 51.60/7.00  --bmc1_ucm_cone_mode                    none
% 51.60/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.60/7.00  --bmc1_ucm_relax_model                  4
% 51.60/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.60/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.60/7.00  --bmc1_ucm_layered_model                none
% 51.60/7.00  --bmc1_ucm_max_lemma_size               10
% 51.60/7.00  
% 51.60/7.00  ------ AIG Options
% 51.60/7.00  
% 51.60/7.00  --aig_mode                              false
% 51.60/7.00  
% 51.60/7.00  ------ Instantiation Options
% 51.60/7.00  
% 51.60/7.00  --instantiation_flag                    false
% 51.60/7.00  --inst_sos_flag                         true
% 51.60/7.00  --inst_sos_phase                        true
% 51.60/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.60/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.60/7.00  --inst_lit_sel_side                     num_symb
% 51.60/7.00  --inst_solver_per_active                1400
% 51.60/7.00  --inst_solver_calls_frac                1.
% 51.60/7.00  --inst_passive_queue_type               priority_queues
% 51.60/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.60/7.00  --inst_passive_queues_freq              [25;2]
% 51.60/7.00  --inst_dismatching                      true
% 51.60/7.00  --inst_eager_unprocessed_to_passive     true
% 51.60/7.00  --inst_prop_sim_given                   true
% 51.60/7.00  --inst_prop_sim_new                     false
% 51.60/7.00  --inst_subs_new                         false
% 51.60/7.00  --inst_eq_res_simp                      false
% 51.60/7.00  --inst_subs_given                       false
% 51.60/7.00  --inst_orphan_elimination               true
% 51.60/7.00  --inst_learning_loop_flag               true
% 51.60/7.00  --inst_learning_start                   3000
% 51.60/7.00  --inst_learning_factor                  2
% 51.60/7.00  --inst_start_prop_sim_after_learn       3
% 51.60/7.00  --inst_sel_renew                        solver
% 51.60/7.00  --inst_lit_activity_flag                true
% 51.60/7.00  --inst_restr_to_given                   false
% 51.60/7.00  --inst_activity_threshold               500
% 51.60/7.00  --inst_out_proof                        true
% 51.60/7.00  
% 51.60/7.00  ------ Resolution Options
% 51.60/7.00  
% 51.60/7.00  --resolution_flag                       false
% 51.60/7.00  --res_lit_sel                           adaptive
% 51.60/7.00  --res_lit_sel_side                      none
% 51.60/7.00  --res_ordering                          kbo
% 51.60/7.00  --res_to_prop_solver                    active
% 51.60/7.00  --res_prop_simpl_new                    false
% 51.60/7.00  --res_prop_simpl_given                  true
% 51.60/7.00  --res_passive_queue_type                priority_queues
% 51.60/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.60/7.00  --res_passive_queues_freq               [15;5]
% 51.60/7.00  --res_forward_subs                      full
% 51.60/7.00  --res_backward_subs                     full
% 51.60/7.00  --res_forward_subs_resolution           true
% 51.60/7.00  --res_backward_subs_resolution          true
% 51.60/7.00  --res_orphan_elimination                true
% 51.60/7.00  --res_time_limit                        2.
% 51.60/7.00  --res_out_proof                         true
% 51.60/7.00  
% 51.60/7.00  ------ Superposition Options
% 51.60/7.00  
% 51.60/7.00  --superposition_flag                    true
% 51.60/7.00  --sup_passive_queue_type                priority_queues
% 51.60/7.00  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.60/7.00  --sup_passive_queues_freq               [8;1;4]
% 51.60/7.00  --demod_completeness_check              fast
% 51.60/7.00  --demod_use_ground                      true
% 51.60/7.00  --sup_to_prop_solver                    active
% 51.60/7.00  --sup_prop_simpl_new                    false
% 51.60/7.00  --sup_prop_simpl_given                  false
% 51.60/7.00  --sup_fun_splitting                     true
% 51.60/7.00  --sup_smt_interval                      10000
% 51.60/7.00  
% 51.60/7.00  ------ Superposition Simplification Setup
% 51.60/7.00  
% 51.60/7.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.60/7.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.60/7.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.60/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.60/7.00  --sup_full_triv                         [TrivRules]
% 51.60/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.60/7.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.60/7.00  --sup_immed_triv                        [TrivRules]
% 51.60/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.60/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.60/7.00  --sup_immed_bw_main                     []
% 51.60/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.60/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.60/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.60/7.00  --sup_input_bw                          [BwDemod;BwSubsumption]
% 51.60/7.00  
% 51.60/7.00  ------ Combination Options
% 51.60/7.00  
% 51.60/7.00  --comb_res_mult                         1
% 51.60/7.00  --comb_sup_mult                         1
% 51.60/7.00  --comb_inst_mult                        1000000
% 51.60/7.00  
% 51.60/7.00  ------ Debug Options
% 51.60/7.00  
% 51.60/7.00  --dbg_backtrace                         false
% 51.60/7.00  --dbg_dump_prop_clauses                 false
% 51.60/7.00  --dbg_dump_prop_clauses_file            -
% 51.60/7.00  --dbg_out_stat                          false
% 51.60/7.00  
% 51.60/7.00  
% 51.60/7.00  
% 51.60/7.00  
% 51.60/7.00  ------ Proving...
% 51.60/7.00  
% 51.60/7.00  
% 51.60/7.00  % SZS status Theorem for theBenchmark.p
% 51.60/7.00  
% 51.60/7.00   Resolution empty clause
% 51.60/7.00  
% 51.60/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 51.60/7.00  
% 51.60/7.00  fof(f2,axiom,(
% 51.60/7.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 51.60/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.60/7.00  
% 51.60/7.00  fof(f22,plain,(
% 51.60/7.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 51.60/7.00    inference(cnf_transformation,[],[f2])).
% 51.60/7.00  
% 51.60/7.00  fof(f11,axiom,(
% 51.60/7.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 51.60/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.60/7.00  
% 51.60/7.00  fof(f31,plain,(
% 51.60/7.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 51.60/7.00    inference(cnf_transformation,[],[f11])).
% 51.60/7.00  
% 51.60/7.00  fof(f35,plain,(
% 51.60/7.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 51.60/7.00    inference(definition_unfolding,[],[f22,f31,f31])).
% 51.60/7.00  
% 51.60/7.00  fof(f1,axiom,(
% 51.60/7.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 51.60/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.60/7.00  
% 51.60/7.00  fof(f21,plain,(
% 51.60/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 51.60/7.00    inference(cnf_transformation,[],[f1])).
% 51.60/7.00  
% 51.60/7.00  fof(f7,axiom,(
% 51.60/7.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 51.60/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.60/7.00  
% 51.60/7.00  fof(f27,plain,(
% 51.60/7.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 51.60/7.00    inference(cnf_transformation,[],[f7])).
% 51.60/7.00  
% 51.60/7.00  fof(f37,plain,(
% 51.60/7.00    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 51.60/7.00    inference(definition_unfolding,[],[f27,f31])).
% 51.60/7.00  
% 51.60/7.00  fof(f9,axiom,(
% 51.60/7.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 51.60/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.60/7.00  
% 51.60/7.00  fof(f29,plain,(
% 51.60/7.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.60/7.00    inference(cnf_transformation,[],[f9])).
% 51.60/7.00  
% 51.60/7.00  fof(f10,axiom,(
% 51.60/7.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 51.60/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.60/7.00  
% 51.60/7.00  fof(f30,plain,(
% 51.60/7.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 51.60/7.00    inference(cnf_transformation,[],[f10])).
% 51.60/7.00  
% 51.60/7.00  fof(f4,axiom,(
% 51.60/7.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 51.60/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.60/7.00  
% 51.60/7.00  fof(f16,plain,(
% 51.60/7.00    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 51.60/7.00    inference(unused_predicate_definition_removal,[],[f4])).
% 51.60/7.00  
% 51.60/7.00  fof(f17,plain,(
% 51.60/7.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 51.60/7.00    inference(ennf_transformation,[],[f16])).
% 51.60/7.00  
% 51.60/7.00  fof(f24,plain,(
% 51.60/7.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 51.60/7.00    inference(cnf_transformation,[],[f17])).
% 51.60/7.00  
% 51.60/7.00  fof(f8,axiom,(
% 51.60/7.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 51.60/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.60/7.00  
% 51.60/7.00  fof(f28,plain,(
% 51.60/7.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 51.60/7.00    inference(cnf_transformation,[],[f8])).
% 51.60/7.00  
% 51.60/7.00  fof(f5,axiom,(
% 51.60/7.00    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2))),
% 51.60/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.60/7.00  
% 51.60/7.00  fof(f25,plain,(
% 51.60/7.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 51.60/7.00    inference(cnf_transformation,[],[f5])).
% 51.60/7.00  
% 51.60/7.00  fof(f36,plain,(
% 51.60/7.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 51.60/7.00    inference(definition_unfolding,[],[f25,f31])).
% 51.60/7.00  
% 51.60/7.00  fof(f12,axiom,(
% 51.60/7.00    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 51.60/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.60/7.00  
% 51.60/7.00  fof(f32,plain,(
% 51.60/7.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 51.60/7.00    inference(cnf_transformation,[],[f12])).
% 51.60/7.00  
% 51.60/7.00  fof(f38,plain,(
% 51.60/7.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 51.60/7.00    inference(definition_unfolding,[],[f32,f31,f31])).
% 51.60/7.00  
% 51.60/7.00  fof(f13,axiom,(
% 51.60/7.00    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 51.60/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.60/7.00  
% 51.60/7.00  fof(f33,plain,(
% 51.60/7.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 51.60/7.00    inference(cnf_transformation,[],[f13])).
% 51.60/7.00  
% 51.60/7.00  fof(f39,plain,(
% 51.60/7.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 51.60/7.00    inference(definition_unfolding,[],[f33,f31])).
% 51.60/7.00  
% 51.60/7.00  fof(f6,axiom,(
% 51.60/7.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 51.60/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.60/7.00  
% 51.60/7.00  fof(f26,plain,(
% 51.60/7.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.60/7.00    inference(cnf_transformation,[],[f6])).
% 51.60/7.00  
% 51.60/7.00  fof(f14,conjecture,(
% 51.60/7.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 51.60/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.60/7.00  
% 51.60/7.00  fof(f15,negated_conjecture,(
% 51.60/7.00    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 51.60/7.00    inference(negated_conjecture,[],[f14])).
% 51.60/7.00  
% 51.60/7.00  fof(f18,plain,(
% 51.60/7.00    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 51.60/7.00    inference(ennf_transformation,[],[f15])).
% 51.60/7.00  
% 51.60/7.00  fof(f19,plain,(
% 51.60/7.00    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 51.60/7.00    introduced(choice_axiom,[])).
% 51.60/7.00  
% 51.60/7.00  fof(f20,plain,(
% 51.60/7.00    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 51.60/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 51.60/7.00  
% 51.60/7.00  fof(f34,plain,(
% 51.60/7.00    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 51.60/7.00    inference(cnf_transformation,[],[f20])).
% 51.60/7.00  
% 51.60/7.00  fof(f3,axiom,(
% 51.60/7.00    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 51.60/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.60/7.00  
% 51.60/7.00  fof(f23,plain,(
% 51.60/7.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 51.60/7.00    inference(cnf_transformation,[],[f3])).
% 51.60/7.00  
% 51.60/7.00  fof(f40,plain,(
% 51.60/7.00    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 51.60/7.00    inference(definition_unfolding,[],[f34,f31,f23,f23])).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 51.60/7.00      inference(cnf_transformation,[],[f35]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_0,plain,
% 51.60/7.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 51.60/7.00      inference(cnf_transformation,[],[f21]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_5,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 51.60/7.00      inference(cnf_transformation,[],[f37]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_7,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.60/7.00      inference(cnf_transformation,[],[f29]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_65,plain,
% 51.60/7.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 51.60/7.00      inference(light_normalisation,[status(thm)],[c_5,c_7]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_8,plain,
% 51.60/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 51.60/7.00      inference(cnf_transformation,[],[f30]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_136,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_65,c_8]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_2,plain,
% 51.60/7.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 51.60/7.00      inference(cnf_transformation,[],[f24]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_6,plain,
% 51.60/7.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 51.60/7.00      inference(cnf_transformation,[],[f28]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_48,plain,
% 51.60/7.00      ( X0 != X1
% 51.60/7.00      | k4_xboole_0(X0,X2) != X3
% 51.60/7.00      | k4_xboole_0(X3,X1) = k1_xboole_0 ),
% 51.60/7.00      inference(resolution_lifted,[status(thm)],[c_2,c_6]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_49,plain,
% 51.60/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 51.60/7.00      inference(unflattening,[status(thm)],[c_48]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_83,plain,
% 51.60/7.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_49,c_7]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_155,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_136,c_83]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_3,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 51.60/7.00      inference(cnf_transformation,[],[f36]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_183,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_7,c_3]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_216,plain,
% 51.60/7.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_183,c_7,c_65]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_366,plain,
% 51.60/7.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_1,c_216]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1034,plain,
% 51.60/7.00      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_155,c_366]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1059,plain,
% 51.60/7.00      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 51.60/7.00      inference(light_normalisation,[status(thm)],[c_1034,c_7]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1669,plain,
% 51.60/7.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_0,c_1059]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_9,plain,
% 51.60/7.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 51.60/7.00      inference(cnf_transformation,[],[f38]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_66,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_9,c_8]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_118,plain,
% 51.60/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_1,c_66]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_119,plain,
% 51.60/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 51.60/7.00      inference(light_normalisation,[status(thm)],[c_118,c_8]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_177,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_7,c_3]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_221,plain,
% 51.60/7.00      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_177,c_7,c_83]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_147,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_8,c_49]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_10,plain,
% 51.60/7.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 51.60/7.00      inference(cnf_transformation,[],[f39]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_330,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_147,c_10]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_338,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 51.60/7.00      inference(light_normalisation,[status(thm)],[c_330,c_7,c_216]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_825,plain,
% 51.60/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k4_xboole_0(X0,X1) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_221,c_338]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_7289,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X0)),X1)) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_119,c_825]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_7428,plain,
% 51.60/7.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X0)) ),
% 51.60/7.00      inference(light_normalisation,[status(thm)],[c_7289,c_147]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_4,plain,
% 51.60/7.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.60/7.00      inference(cnf_transformation,[],[f26]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_69,plain,
% 51.60/7.00      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_7429,plain,
% 51.60/7.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_7428,c_69]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_8495,plain,
% 51.60/7.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(k2_xboole_0(X1,X0),X0) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_1669,c_7429]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_8623,plain,
% 51.60/7.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_8495,c_7429]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_8956,plain,
% 51.60/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0)))) = k4_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_8623,c_119]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_328,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_147,c_8]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_137,plain,
% 51.60/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_8,c_8]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_154,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_137,c_8]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_339,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_328,c_83,c_154]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_863,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_0,c_339]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_8973,plain,
% 51.60/7.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0) ),
% 51.60/7.00      inference(light_normalisation,[status(thm)],[c_8956,c_863]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_8974,plain,
% 51.60/7.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_8973,c_4,c_8]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_11,negated_conjecture,
% 51.60/7.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 51.60/7.00      inference(cnf_transformation,[],[f40]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_68,plain,
% 51.60/7.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_0,c_11]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_139324,plain,
% 51.60/7.00      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_8974,c_68]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_8542,plain,
% 51.60/7.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_7429,c_1]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_8595,plain,
% 51.60/7.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 51.60/7.00      inference(light_normalisation,[status(thm)],[c_8542,c_7,c_155]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_256,plain,
% 51.60/7.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_65,c_10]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_261,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 51.60/7.00      inference(light_normalisation,[status(thm)],[c_256,c_7,c_216]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_428,plain,
% 51.60/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_261,c_261]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1195,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X2)) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_428,c_3]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1206,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X2)) ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_1195,c_8]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_148,plain,
% 51.60/7.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_8,c_65]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1207,plain,
% 51.60/7.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X2)) = X0 ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_1206,c_7,c_148]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_8763,plain,
% 51.60/7.00      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X0)) = k2_xboole_0(X0,X1) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_8595,c_1207]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_8784,plain,
% 51.60/7.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 51.60/7.00      inference(light_normalisation,[status(thm)],[c_8763,c_7429]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_135,plain,
% 51.60/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_49,c_8]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_156,plain,
% 51.60/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_135,c_8,c_83]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_755,plain,
% 51.60/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_0,c_156]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_8704,plain,
% 51.60/7.00      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(X0,X1) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_755,c_8595]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_394,plain,
% 51.60/7.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_1,c_221]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1107,plain,
% 51.60/7.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k1_xboole_0)) = k2_xboole_0(X0,X1) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_156,c_394]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1138,plain,
% 51.60/7.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X2,k1_xboole_0))) = k2_xboole_0(X0,X1) ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_1107,c_8]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1139,plain,
% 51.60/7.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_1138,c_4]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_8021,plain,
% 51.60/7.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,X0) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_0,c_1139]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_8813,plain,
% 51.60/7.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 51.60/7.00      inference(light_normalisation,[status(thm)],[c_8704,c_8021]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_9373,plain,
% 51.60/7.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_8784,c_8813]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_9507,plain,
% 51.60/7.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_9373,c_8813]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_431,plain,
% 51.60/7.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_261,c_3]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_442,plain,
% 51.60/7.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1))) = X0 ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_431,c_7,c_65]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_4776,plain,
% 51.60/7.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_1,c_442]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1101,plain,
% 51.60/7.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(X0,X1) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_147,c_394]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1146,plain,
% 51.60/7.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_1101,c_7]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1777,plain,
% 51.60/7.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_0,c_1146]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1827,plain,
% 51.60/7.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_1669,c_339]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_16964,plain,
% 51.60/7.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X1,X0)),X2)) = k1_xboole_0 ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_1777,c_1827]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1027,plain,
% 51.60/7.00      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_147,c_366]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1068,plain,
% 51.60/7.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 51.60/7.00      inference(light_normalisation,[status(thm)],[c_1027,c_7]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1697,plain,
% 51.60/7.00      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_0,c_1068]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1282,plain,
% 51.60/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),X3)) = k4_xboole_0(k1_xboole_0,X3) ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_755,c_8]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_1309,plain,
% 51.60/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),X3)) = k1_xboole_0 ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_1282,c_8,c_83]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_10639,plain,
% 51.60/7.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,k2_xboole_0(X1,X0)),X3)) = k1_xboole_0 ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_8813,c_1309]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_17212,plain,
% 51.60/7.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_16964,c_154,c_1697,c_10639]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_33218,plain,
% 51.60/7.00      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_4776,c_17212]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_37434,plain,
% 51.60/7.00      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_9507,c_33218]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_139325,plain,
% 51.60/7.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 51.60/7.00      inference(demodulation,[status(thm)],[c_139324,c_4,c_37434]) ).
% 51.60/7.00  
% 51.60/7.00  cnf(c_140379,plain,
% 51.60/7.00      ( $false ),
% 51.60/7.00      inference(superposition,[status(thm)],[c_1,c_139325]) ).
% 51.60/7.00  
% 51.60/7.00  
% 51.60/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 51.60/7.00  
% 51.60/7.00  ------                               Statistics
% 51.60/7.00  
% 51.60/7.00  ------ General
% 51.60/7.00  
% 51.60/7.00  abstr_ref_over_cycles:                  0
% 51.60/7.00  abstr_ref_under_cycles:                 0
% 51.60/7.00  gc_basic_clause_elim:                   0
% 51.60/7.00  forced_gc_time:                         0
% 51.60/7.00  parsing_time:                           0.004
% 51.60/7.00  unif_index_cands_time:                  0.
% 51.60/7.00  unif_index_add_time:                    0.
% 51.60/7.00  orderings_time:                         0.
% 51.60/7.00  out_proof_time:                         0.007
% 51.60/7.00  total_time:                             6.448
% 51.60/7.00  num_of_symbols:                         39
% 51.60/7.00  num_of_terms:                           399081
% 51.60/7.00  
% 51.60/7.00  ------ Preprocessing
% 51.60/7.00  
% 51.60/7.00  num_of_splits:                          0
% 51.60/7.00  num_of_split_atoms:                     2
% 51.60/7.00  num_of_reused_defs:                     4
% 51.60/7.00  num_eq_ax_congr_red:                    1
% 51.60/7.00  num_of_sem_filtered_clauses:            0
% 51.60/7.00  num_of_subtypes:                        0
% 51.60/7.00  monotx_restored_types:                  0
% 51.60/7.00  sat_num_of_epr_types:                   0
% 51.60/7.00  sat_num_of_non_cyclic_types:            0
% 51.60/7.00  sat_guarded_non_collapsed_types:        0
% 51.60/7.00  num_pure_diseq_elim:                    0
% 51.60/7.00  simp_replaced_by:                       0
% 51.60/7.00  res_preprocessed:                       38
% 51.60/7.00  prep_upred:                             0
% 51.60/7.00  prep_unflattend:                        2
% 51.60/7.00  smt_new_axioms:                         0
% 51.60/7.00  pred_elim_cands:                        0
% 51.60/7.00  pred_elim:                              1
% 51.60/7.00  pred_elim_cl:                           1
% 51.60/7.00  pred_elim_cycles:                       2
% 51.60/7.00  merged_defs:                            0
% 51.60/7.00  merged_defs_ncl:                        0
% 51.60/7.00  bin_hyper_res:                          0
% 51.60/7.00  prep_cycles:                            3
% 51.60/7.00  pred_elim_time:                         0.
% 51.60/7.00  splitting_time:                         0.
% 51.60/7.00  sem_filter_time:                        0.
% 51.60/7.00  monotx_time:                            0.
% 51.60/7.00  subtype_inf_time:                       0.
% 51.60/7.00  
% 51.60/7.00  ------ Problem properties
% 51.60/7.00  
% 51.60/7.00  clauses:                                11
% 51.60/7.00  conjectures:                            1
% 51.60/7.00  epr:                                    0
% 51.60/7.00  horn:                                   11
% 51.60/7.00  ground:                                 1
% 51.60/7.00  unary:                                  11
% 51.60/7.00  binary:                                 0
% 51.60/7.00  lits:                                   11
% 51.60/7.00  lits_eq:                                11
% 51.60/7.00  fd_pure:                                0
% 51.60/7.00  fd_pseudo:                              0
% 51.60/7.00  fd_cond:                                0
% 51.60/7.00  fd_pseudo_cond:                         0
% 51.60/7.00  ac_symbols:                             0
% 51.60/7.00  
% 51.60/7.00  ------ Propositional Solver
% 51.60/7.00  
% 51.60/7.00  prop_solver_calls:                      17
% 51.60/7.00  prop_fast_solver_calls:                 91
% 51.60/7.00  smt_solver_calls:                       0
% 51.60/7.00  smt_fast_solver_calls:                  0
% 51.60/7.00  prop_num_of_clauses:                    472
% 51.60/7.00  prop_preprocess_simplified:             626
% 51.60/7.00  prop_fo_subsumed:                       0
% 51.60/7.00  prop_solver_time:                       0.
% 51.60/7.00  smt_solver_time:                        0.
% 51.60/7.00  smt_fast_solver_time:                   0.
% 51.60/7.00  prop_fast_solver_time:                  0.
% 51.60/7.00  prop_unsat_core_time:                   0.
% 51.60/7.00  
% 51.60/7.00  ------ QBF
% 51.60/7.00  
% 51.60/7.00  qbf_q_res:                              0
% 51.60/7.00  qbf_num_tautologies:                    0
% 51.60/7.00  qbf_prep_cycles:                        0
% 51.60/7.00  
% 51.60/7.00  ------ BMC1
% 51.60/7.00  
% 51.60/7.00  bmc1_current_bound:                     -1
% 51.60/7.00  bmc1_last_solved_bound:                 -1
% 51.60/7.00  bmc1_unsat_core_size:                   -1
% 51.60/7.00  bmc1_unsat_core_parents_size:           -1
% 51.60/7.00  bmc1_merge_next_fun:                    0
% 51.60/7.00  bmc1_unsat_core_clauses_time:           0.
% 51.60/7.00  
% 51.60/7.00  ------ Instantiation
% 51.60/7.00  
% 51.60/7.00  inst_num_of_clauses:                    0
% 51.60/7.00  inst_num_in_passive:                    0
% 51.60/7.00  inst_num_in_active:                     0
% 51.60/7.00  inst_num_in_unprocessed:                0
% 51.60/7.00  inst_num_of_loops:                      0
% 51.60/7.00  inst_num_of_learning_restarts:          0
% 51.60/7.00  inst_num_moves_active_passive:          0
% 51.60/7.00  inst_lit_activity:                      0
% 51.60/7.00  inst_lit_activity_moves:                0
% 51.60/7.00  inst_num_tautologies:                   0
% 51.60/7.00  inst_num_prop_implied:                  0
% 51.60/7.00  inst_num_existing_simplified:           0
% 51.60/7.00  inst_num_eq_res_simplified:             0
% 51.60/7.00  inst_num_child_elim:                    0
% 51.60/7.00  inst_num_of_dismatching_blockings:      0
% 51.60/7.00  inst_num_of_non_proper_insts:           0
% 51.60/7.00  inst_num_of_duplicates:                 0
% 51.60/7.00  inst_inst_num_from_inst_to_res:         0
% 51.60/7.00  inst_dismatching_checking_time:         0.
% 51.60/7.00  
% 51.60/7.00  ------ Resolution
% 51.60/7.00  
% 51.60/7.00  res_num_of_clauses:                     0
% 51.60/7.00  res_num_in_passive:                     0
% 51.60/7.00  res_num_in_active:                      0
% 51.60/7.00  res_num_of_loops:                       41
% 51.60/7.00  res_forward_subset_subsumed:            0
% 51.60/7.00  res_backward_subset_subsumed:           0
% 51.60/7.00  res_forward_subsumed:                   0
% 51.60/7.00  res_backward_subsumed:                  0
% 51.60/7.00  res_forward_subsumption_resolution:     0
% 51.60/7.00  res_backward_subsumption_resolution:    0
% 51.60/7.00  res_clause_to_clause_subsumption:       635935
% 51.60/7.00  res_orphan_elimination:                 0
% 51.60/7.00  res_tautology_del:                      0
% 51.60/7.00  res_num_eq_res_simplified:              0
% 51.60/7.00  res_num_sel_changes:                    0
% 51.60/7.00  res_moves_from_active_to_pass:          0
% 51.60/7.00  
% 51.60/7.00  ------ Superposition
% 51.60/7.00  
% 51.60/7.00  sup_time_total:                         0.
% 51.60/7.00  sup_time_generating:                    0.
% 51.60/7.00  sup_time_sim_full:                      0.
% 51.60/7.00  sup_time_sim_immed:                     0.
% 51.60/7.00  
% 51.60/7.00  sup_num_of_clauses:                     18577
% 51.60/7.00  sup_num_in_active:                      249
% 51.60/7.00  sup_num_in_passive:                     18328
% 51.60/7.00  sup_num_of_loops:                       272
% 51.60/7.00  sup_fw_superposition:                   47689
% 51.60/7.00  sup_bw_superposition:                   37973
% 51.60/7.00  sup_immediate_simplified:               45649
% 51.60/7.00  sup_given_eliminated:                   7
% 51.60/7.00  comparisons_done:                       0
% 51.60/7.00  comparisons_avoided:                    0
% 51.60/7.00  
% 51.60/7.00  ------ Simplifications
% 51.60/7.00  
% 51.60/7.00  
% 51.60/7.00  sim_fw_subset_subsumed:                 0
% 51.60/7.00  sim_bw_subset_subsumed:                 0
% 51.60/7.00  sim_fw_subsumed:                        6046
% 51.60/7.00  sim_bw_subsumed:                        202
% 51.60/7.00  sim_fw_subsumption_res:                 0
% 51.60/7.00  sim_bw_subsumption_res:                 0
% 51.60/7.00  sim_tautology_del:                      0
% 51.60/7.00  sim_eq_tautology_del:                   12933
% 51.60/7.00  sim_eq_res_simp:                        0
% 51.60/7.00  sim_fw_demodulated:                     36712
% 51.60/7.00  sim_bw_demodulated:                     538
% 51.60/7.00  sim_light_normalised:                   17221
% 51.60/7.00  sim_joinable_taut:                      0
% 51.60/7.00  sim_joinable_simp:                      0
% 51.60/7.00  sim_ac_normalised:                      0
% 51.60/7.00  sim_smt_subsumption:                    0
% 51.60/7.00  
%------------------------------------------------------------------------------
