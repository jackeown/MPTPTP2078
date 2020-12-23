%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0107+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:21 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 145 expanded)
%              Number of clauses        :   24 (  43 expanded)
%              Number of leaves         :   13 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :   61 ( 146 expanded)
%              Number of equality atoms :   60 ( 145 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f437,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f90])).

fof(f91,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f438,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f91])).

fof(f584,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f437,f438])).

fof(f151,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f502,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f151])).

fof(f147,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f498,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f147])).

fof(f505,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f498,f438])).

fof(f624,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f502,f505])).

fof(f144,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f495,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f144])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f315,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f105,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f452,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f105])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f318,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f594,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f452,f318])).

fof(f145,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f496,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f145])).

fof(f621,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f496,f318])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f340,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f506,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f340,f505])).

fof(f93,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f440,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f93])).

fof(f586,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f440,f318,f318])).

fof(f45,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f45])).

fof(f176,plain,(
    ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f46])).

fof(f303,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1)
   => k5_xboole_0(sK13,k3_xboole_0(sK13,sK14)) != k4_xboole_0(sK13,sK14) ),
    introduced(choice_axiom,[])).

fof(f304,plain,(
    k5_xboole_0(sK13,k3_xboole_0(sK13,sK14)) != k4_xboole_0(sK13,sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f176,f303])).

fof(f388,plain,(
    k5_xboole_0(sK13,k3_xboole_0(sK13,sK14)) != k4_xboole_0(sK13,sK14) ),
    inference(cnf_transformation,[],[f304])).

fof(f541,plain,(
    k5_xboole_0(sK13,k4_xboole_0(sK13,k4_xboole_0(sK13,sK14))) != k4_xboole_0(sK13,sK14) ),
    inference(definition_unfolding,[],[f388,f438])).

cnf(c_125,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f584])).

cnf(c_188,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f624])).

cnf(c_182,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f495])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f315])).

cnf(c_2931,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_188,c_182,c_5])).

cnf(c_6953,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_125,c_2931])).

cnf(c_139,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f594])).

cnf(c_183,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f621])).

cnf(c_6956,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_6953,c_139,c_183])).

cnf(c_6986,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_183,c_182])).

cnf(c_6905,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_139,c_5])).

cnf(c_8077,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_6986,c_6905])).

cnf(c_8092,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_6956,c_8077])).

cnf(c_8110,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8092,c_183])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f506])).

cnf(c_2991,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))))) = k5_xboole_0(X0,X1) ),
    inference(theory_normalisation,[status(thm)],[c_0,c_182,c_5])).

cnf(c_8488,plain,
    ( k5_xboole_0(o_0_0_xboole_0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(o_0_0_xboole_0,k4_xboole_0(o_0_0_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k5_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_8110,c_2991])).

cnf(c_127,plain,
    ( k4_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f586])).

cnf(c_8543,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_8488,c_127,c_139,c_6905])).

cnf(c_76,negated_conjecture,
    ( k5_xboole_0(sK13,k4_xboole_0(sK13,k4_xboole_0(sK13,sK14))) != k4_xboole_0(sK13,sK14) ),
    inference(cnf_transformation,[],[f541])).

cnf(c_17352,plain,
    ( k5_xboole_0(sK13,k5_xboole_0(k4_xboole_0(sK13,sK14),sK13)) != k4_xboole_0(sK13,sK14) ),
    inference(demodulation,[status(thm)],[c_8543,c_76])).

cnf(c_8084,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_5,c_8077])).

cnf(c_17355,plain,
    ( k4_xboole_0(sK13,sK14) != k4_xboole_0(sK13,sK14) ),
    inference(demodulation,[status(thm)],[c_17352,c_8084])).

cnf(c_17356,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_17355])).

%------------------------------------------------------------------------------
