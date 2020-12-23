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
% DateTime   : Thu Dec  3 11:27:52 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 326 expanded)
%              Number of clauses        :   30 (  62 expanded)
%              Number of leaves         :   12 ( 109 expanded)
%              Depth                    :   13
%              Number of atoms          :   66 ( 327 expanded)
%              Number of equality atoms :   65 ( 326 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f24,f22,f32])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f29,f22,f32,f38])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2))) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f23,f22,f32,f32])).

fof(f40,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f33,f37])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f21,f22,f22])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f25,f37,f37])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X0,X3),k4_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3))) ),
    inference(definition_unfolding,[],[f26,f37,f37])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f17])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).

fof(f36,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) ),
    inference(definition_unfolding,[],[f36,f37,f37])).

cnf(c_6,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_30,plain,
    ( k5_xboole_0(k1_enumset1(X0_38,X0_38,X1_38),k4_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X0_38,X1_38))) = k5_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k4_xboole_0(k1_enumset1(X3_38,X3_38,X4_38),k1_enumset1(X0_38,X1_38,X2_38))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_9,plain,
    ( k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2))) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_28,plain,
    ( k5_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k4_xboole_0(k1_enumset1(X3_38,X3_38,X4_38),k1_enumset1(X0_38,X1_38,X2_38))) = k4_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X4_38) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_54,plain,
    ( k5_xboole_0(k1_enumset1(X0_38,X0_38,X1_38),k4_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X0_38,X1_38))) = k4_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X4_38) ),
    inference(light_normalisation,[status(thm)],[c_30,c_28])).

cnf(c_405,plain,
    ( k4_enumset1(X0_38,X0_38,X1_38,X2_38,X2_38,X3_38) = k4_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38,X3_38) ),
    inference(superposition,[status(thm)],[c_54,c_28])).

cnf(c_0,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_36,plain,
    ( k5_xboole_0(k1_enumset1(X0_38,X0_38,X0_38),k4_xboole_0(k1_enumset1(X1_38,X1_38,X2_38),k1_enumset1(X0_38,X0_38,X0_38))) = k1_enumset1(X0_38,X1_38,X2_38) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_408,plain,
    ( k4_enumset1(X0_38,X0_38,X0_38,X1_38,X1_38,X2_38) = k1_enumset1(X0_38,X1_38,X2_38) ),
    inference(superposition,[status(thm)],[c_54,c_36])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_35,plain,
    ( k5_xboole_0(X0_36,k4_xboole_0(X1_36,X0_36)) = k5_xboole_0(X1_36,k4_xboole_0(X0_36,X1_36)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_146,plain,
    ( k5_xboole_0(k1_enumset1(X0_38,X0_38,X1_38),k4_xboole_0(k1_enumset1(X2_38,X2_38,X2_38),k1_enumset1(X0_38,X0_38,X1_38))) = k1_enumset1(X2_38,X0_38,X1_38) ),
    inference(superposition,[status(thm)],[c_35,c_36])).

cnf(c_181,plain,
    ( k4_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38,X2_38) = k1_enumset1(X2_38,X0_38,X1_38) ),
    inference(superposition,[status(thm)],[c_146,c_28])).

cnf(c_2,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_34,plain,
    ( k5_xboole_0(k1_enumset1(X0_38,X0_38,X1_38),k4_xboole_0(k1_enumset1(X2_38,X2_38,X3_38),k1_enumset1(X0_38,X0_38,X1_38))) = k5_xboole_0(k1_enumset1(X0_38,X0_38,X1_38),k4_xboole_0(k1_enumset1(X3_38,X3_38,X2_38),k1_enumset1(X0_38,X0_38,X1_38))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_52,plain,
    ( k4_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38,X3_38) = k4_enumset1(X0_38,X0_38,X0_38,X1_38,X3_38,X2_38) ),
    inference(demodulation,[status(thm)],[c_34,c_28])).

cnf(c_3,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X0,X3),k4_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_33,plain,
    ( k5_xboole_0(k1_enumset1(X0_38,X0_38,X1_38),k4_xboole_0(k1_enumset1(X2_38,X2_38,X3_38),k1_enumset1(X0_38,X0_38,X1_38))) = k5_xboole_0(k1_enumset1(X0_38,X0_38,X3_38),k4_xboole_0(k1_enumset1(X2_38,X2_38,X1_38),k1_enumset1(X0_38,X0_38,X3_38))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_53,plain,
    ( k4_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38,X3_38) = k4_enumset1(X0_38,X0_38,X0_38,X3_38,X2_38,X1_38) ),
    inference(demodulation,[status(thm)],[c_33,c_28])).

cnf(c_62,plain,
    ( k4_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38,X3_38) = k4_enumset1(X0_38,X0_38,X0_38,X3_38,X1_38,X2_38) ),
    inference(superposition,[status(thm)],[c_52,c_53])).

cnf(c_206,plain,
    ( k4_enumset1(X0_38,X0_38,X0_38,X1_38,X1_38,X2_38) = k1_enumset1(X1_38,X0_38,X2_38) ),
    inference(superposition,[status(thm)],[c_181,c_62])).

cnf(c_433,plain,
    ( k1_enumset1(X0_38,X1_38,X2_38) = k1_enumset1(X1_38,X0_38,X2_38) ),
    inference(superposition,[status(thm)],[c_408,c_206])).

cnf(c_573,plain,
    ( k5_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k4_xboole_0(k1_enumset1(X3_38,X3_38,X4_38),k1_enumset1(X0_38,X1_38,X2_38))) = k4_enumset1(X1_38,X1_38,X0_38,X2_38,X3_38,X4_38) ),
    inference(superposition,[status(thm)],[c_433,c_28])).

cnf(c_2848,plain,
    ( k4_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X4_38) = k4_enumset1(X1_38,X1_38,X0_38,X2_38,X3_38,X4_38) ),
    inference(superposition,[status(thm)],[c_573,c_28])).

cnf(c_10,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_27,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_56,plain,
    ( k4_enumset1(sK1,sK1,sK0,sK2,sK2,sK3) != k4_enumset1(sK0,sK0,sK1,sK2,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_27,c_54])).

cnf(c_440,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK1,sK1,sK0,sK2,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_405,c_56])).

cnf(c_2862,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK1,sK2,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_2848,c_440])).

cnf(c_2937,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_405,c_2862])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:58:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.53/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.53/0.99  
% 1.53/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.53/0.99  
% 1.53/0.99  ------  iProver source info
% 1.53/0.99  
% 1.53/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.53/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.53/0.99  git: non_committed_changes: false
% 1.53/0.99  git: last_make_outside_of_git: false
% 1.53/0.99  
% 1.53/0.99  ------ 
% 1.53/0.99  
% 1.53/0.99  ------ Input Options
% 1.53/0.99  
% 1.53/0.99  --out_options                           all
% 1.53/0.99  --tptp_safe_out                         true
% 1.53/0.99  --problem_path                          ""
% 1.53/0.99  --include_path                          ""
% 1.53/0.99  --clausifier                            res/vclausify_rel
% 1.53/0.99  --clausifier_options                    --mode clausify
% 1.53/0.99  --stdin                                 false
% 1.53/0.99  --stats_out                             all
% 1.53/0.99  
% 1.53/0.99  ------ General Options
% 1.53/0.99  
% 1.53/0.99  --fof                                   false
% 1.53/0.99  --time_out_real                         305.
% 1.53/0.99  --time_out_virtual                      -1.
% 1.53/0.99  --symbol_type_check                     false
% 1.53/0.99  --clausify_out                          false
% 1.53/0.99  --sig_cnt_out                           false
% 1.53/0.99  --trig_cnt_out                          false
% 1.53/0.99  --trig_cnt_out_tolerance                1.
% 1.53/0.99  --trig_cnt_out_sk_spl                   false
% 1.53/0.99  --abstr_cl_out                          false
% 1.53/0.99  
% 1.53/0.99  ------ Global Options
% 1.53/0.99  
% 1.53/0.99  --schedule                              default
% 1.53/0.99  --add_important_lit                     false
% 1.53/0.99  --prop_solver_per_cl                    1000
% 1.53/0.99  --min_unsat_core                        false
% 1.53/0.99  --soft_assumptions                      false
% 1.53/0.99  --soft_lemma_size                       3
% 1.53/0.99  --prop_impl_unit_size                   0
% 1.53/0.99  --prop_impl_unit                        []
% 1.53/0.99  --share_sel_clauses                     true
% 1.53/0.99  --reset_solvers                         false
% 1.53/0.99  --bc_imp_inh                            [conj_cone]
% 1.53/0.99  --conj_cone_tolerance                   3.
% 1.53/0.99  --extra_neg_conj                        none
% 1.53/0.99  --large_theory_mode                     true
% 1.53/0.99  --prolific_symb_bound                   200
% 1.53/0.99  --lt_threshold                          2000
% 1.53/0.99  --clause_weak_htbl                      true
% 1.53/0.99  --gc_record_bc_elim                     false
% 1.53/0.99  
% 1.53/0.99  ------ Preprocessing Options
% 1.53/0.99  
% 1.53/0.99  --preprocessing_flag                    true
% 1.53/0.99  --time_out_prep_mult                    0.1
% 1.53/0.99  --splitting_mode                        input
% 1.53/0.99  --splitting_grd                         true
% 1.53/0.99  --splitting_cvd                         false
% 1.53/0.99  --splitting_cvd_svl                     false
% 1.53/0.99  --splitting_nvd                         32
% 1.53/0.99  --sub_typing                            true
% 1.53/0.99  --prep_gs_sim                           true
% 1.53/0.99  --prep_unflatten                        true
% 1.53/0.99  --prep_res_sim                          true
% 1.53/0.99  --prep_upred                            true
% 1.53/0.99  --prep_sem_filter                       exhaustive
% 1.53/0.99  --prep_sem_filter_out                   false
% 1.53/0.99  --pred_elim                             true
% 1.53/0.99  --res_sim_input                         true
% 1.53/0.99  --eq_ax_congr_red                       true
% 1.53/0.99  --pure_diseq_elim                       true
% 1.53/0.99  --brand_transform                       false
% 1.53/0.99  --non_eq_to_eq                          false
% 1.53/0.99  --prep_def_merge                        true
% 1.53/0.99  --prep_def_merge_prop_impl              false
% 1.53/0.99  --prep_def_merge_mbd                    true
% 1.53/0.99  --prep_def_merge_tr_red                 false
% 1.53/0.99  --prep_def_merge_tr_cl                  false
% 1.53/0.99  --smt_preprocessing                     true
% 1.53/0.99  --smt_ac_axioms                         fast
% 1.53/0.99  --preprocessed_out                      false
% 1.53/0.99  --preprocessed_stats                    false
% 1.53/0.99  
% 1.53/0.99  ------ Abstraction refinement Options
% 1.53/0.99  
% 1.53/0.99  --abstr_ref                             []
% 1.53/0.99  --abstr_ref_prep                        false
% 1.53/0.99  --abstr_ref_until_sat                   false
% 1.53/0.99  --abstr_ref_sig_restrict                funpre
% 1.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.53/0.99  --abstr_ref_under                       []
% 1.53/0.99  
% 1.53/0.99  ------ SAT Options
% 1.53/0.99  
% 1.53/0.99  --sat_mode                              false
% 1.53/0.99  --sat_fm_restart_options                ""
% 1.53/0.99  --sat_gr_def                            false
% 1.53/0.99  --sat_epr_types                         true
% 1.53/0.99  --sat_non_cyclic_types                  false
% 1.53/0.99  --sat_finite_models                     false
% 1.53/0.99  --sat_fm_lemmas                         false
% 1.53/0.99  --sat_fm_prep                           false
% 1.53/0.99  --sat_fm_uc_incr                        true
% 1.53/0.99  --sat_out_model                         small
% 1.53/0.99  --sat_out_clauses                       false
% 1.53/0.99  
% 1.53/0.99  ------ QBF Options
% 1.53/0.99  
% 1.53/0.99  --qbf_mode                              false
% 1.53/0.99  --qbf_elim_univ                         false
% 1.53/0.99  --qbf_dom_inst                          none
% 1.53/0.99  --qbf_dom_pre_inst                      false
% 1.53/0.99  --qbf_sk_in                             false
% 1.53/0.99  --qbf_pred_elim                         true
% 1.53/0.99  --qbf_split                             512
% 1.53/0.99  
% 1.53/0.99  ------ BMC1 Options
% 1.53/0.99  
% 1.53/0.99  --bmc1_incremental                      false
% 1.53/0.99  --bmc1_axioms                           reachable_all
% 1.53/0.99  --bmc1_min_bound                        0
% 1.53/0.99  --bmc1_max_bound                        -1
% 1.53/0.99  --bmc1_max_bound_default                -1
% 1.53/0.99  --bmc1_symbol_reachability              true
% 1.53/0.99  --bmc1_property_lemmas                  false
% 1.53/0.99  --bmc1_k_induction                      false
% 1.53/0.99  --bmc1_non_equiv_states                 false
% 1.53/0.99  --bmc1_deadlock                         false
% 1.53/0.99  --bmc1_ucm                              false
% 1.53/0.99  --bmc1_add_unsat_core                   none
% 1.53/0.99  --bmc1_unsat_core_children              false
% 1.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.53/0.99  --bmc1_out_stat                         full
% 1.53/0.99  --bmc1_ground_init                      false
% 1.53/0.99  --bmc1_pre_inst_next_state              false
% 1.53/0.99  --bmc1_pre_inst_state                   false
% 1.53/0.99  --bmc1_pre_inst_reach_state             false
% 1.53/0.99  --bmc1_out_unsat_core                   false
% 1.53/0.99  --bmc1_aig_witness_out                  false
% 1.53/0.99  --bmc1_verbose                          false
% 1.53/0.99  --bmc1_dump_clauses_tptp                false
% 1.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.53/0.99  --bmc1_dump_file                        -
% 1.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.53/0.99  --bmc1_ucm_extend_mode                  1
% 1.53/0.99  --bmc1_ucm_init_mode                    2
% 1.53/0.99  --bmc1_ucm_cone_mode                    none
% 1.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.53/0.99  --bmc1_ucm_relax_model                  4
% 1.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.53/0.99  --bmc1_ucm_layered_model                none
% 1.53/0.99  --bmc1_ucm_max_lemma_size               10
% 1.53/0.99  
% 1.53/0.99  ------ AIG Options
% 1.53/0.99  
% 1.53/0.99  --aig_mode                              false
% 1.53/0.99  
% 1.53/0.99  ------ Instantiation Options
% 1.53/0.99  
% 1.53/0.99  --instantiation_flag                    true
% 1.53/0.99  --inst_sos_flag                         false
% 1.53/0.99  --inst_sos_phase                        true
% 1.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.53/0.99  --inst_lit_sel_side                     num_symb
% 1.53/0.99  --inst_solver_per_active                1400
% 1.53/0.99  --inst_solver_calls_frac                1.
% 1.53/0.99  --inst_passive_queue_type               priority_queues
% 1.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.53/0.99  --inst_passive_queues_freq              [25;2]
% 1.53/0.99  --inst_dismatching                      true
% 1.53/0.99  --inst_eager_unprocessed_to_passive     true
% 1.53/0.99  --inst_prop_sim_given                   true
% 1.53/0.99  --inst_prop_sim_new                     false
% 1.53/0.99  --inst_subs_new                         false
% 1.53/0.99  --inst_eq_res_simp                      false
% 1.53/0.99  --inst_subs_given                       false
% 1.53/0.99  --inst_orphan_elimination               true
% 1.53/0.99  --inst_learning_loop_flag               true
% 1.53/0.99  --inst_learning_start                   3000
% 1.53/0.99  --inst_learning_factor                  2
% 1.53/0.99  --inst_start_prop_sim_after_learn       3
% 1.53/0.99  --inst_sel_renew                        solver
% 1.53/0.99  --inst_lit_activity_flag                true
% 1.53/0.99  --inst_restr_to_given                   false
% 1.53/0.99  --inst_activity_threshold               500
% 1.53/0.99  --inst_out_proof                        true
% 1.53/0.99  
% 1.53/0.99  ------ Resolution Options
% 1.53/0.99  
% 1.53/0.99  --resolution_flag                       true
% 1.53/0.99  --res_lit_sel                           adaptive
% 1.53/0.99  --res_lit_sel_side                      none
% 1.53/0.99  --res_ordering                          kbo
% 1.53/0.99  --res_to_prop_solver                    active
% 1.53/0.99  --res_prop_simpl_new                    false
% 1.53/0.99  --res_prop_simpl_given                  true
% 1.53/0.99  --res_passive_queue_type                priority_queues
% 1.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.53/0.99  --res_passive_queues_freq               [15;5]
% 1.53/0.99  --res_forward_subs                      full
% 1.53/0.99  --res_backward_subs                     full
% 1.53/0.99  --res_forward_subs_resolution           true
% 1.53/0.99  --res_backward_subs_resolution          true
% 1.53/0.99  --res_orphan_elimination                true
% 1.53/0.99  --res_time_limit                        2.
% 1.53/0.99  --res_out_proof                         true
% 1.53/0.99  
% 1.53/0.99  ------ Superposition Options
% 1.53/0.99  
% 1.53/0.99  --superposition_flag                    true
% 1.53/0.99  --sup_passive_queue_type                priority_queues
% 1.53/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.53/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.53/0.99  --demod_completeness_check              fast
% 1.53/0.99  --demod_use_ground                      true
% 1.53/0.99  --sup_to_prop_solver                    passive
% 1.53/0.99  --sup_prop_simpl_new                    true
% 1.53/0.99  --sup_prop_simpl_given                  true
% 1.53/0.99  --sup_fun_splitting                     false
% 1.53/0.99  --sup_smt_interval                      50000
% 1.53/0.99  
% 1.53/0.99  ------ Superposition Simplification Setup
% 1.53/0.99  
% 1.53/0.99  --sup_indices_passive                   []
% 1.53/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.99  --sup_full_bw                           [BwDemod]
% 1.53/0.99  --sup_immed_triv                        [TrivRules]
% 1.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.99  --sup_immed_bw_main                     []
% 1.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/0.99  
% 1.53/0.99  ------ Combination Options
% 1.53/0.99  
% 1.53/0.99  --comb_res_mult                         3
% 1.53/0.99  --comb_sup_mult                         2
% 1.53/0.99  --comb_inst_mult                        10
% 1.53/0.99  
% 1.53/0.99  ------ Debug Options
% 1.53/0.99  
% 1.53/0.99  --dbg_backtrace                         false
% 1.53/0.99  --dbg_dump_prop_clauses                 false
% 1.53/0.99  --dbg_dump_prop_clauses_file            -
% 1.53/0.99  --dbg_out_stat                          false
% 1.53/0.99  ------ Parsing...
% 1.53/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.53/0.99  
% 1.53/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.53/0.99  
% 1.53/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.53/0.99  
% 1.53/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 1.53/0.99  ------ Proving...
% 1.53/0.99  ------ Problem Properties 
% 1.53/0.99  
% 1.53/0.99  
% 1.53/0.99  clauses                                 10
% 1.53/0.99  conjectures                             1
% 1.53/0.99  EPR                                     0
% 1.53/0.99  Horn                                    10
% 1.53/0.99  unary                                   10
% 1.53/0.99  binary                                  0
% 1.53/0.99  lits                                    10
% 1.53/0.99  lits eq                                 10
% 1.53/0.99  fd_pure                                 0
% 1.53/0.99  fd_pseudo                               0
% 1.53/0.99  fd_cond                                 0
% 1.53/0.99  fd_pseudo_cond                          0
% 1.53/0.99  AC symbols                              0
% 1.53/0.99  
% 1.53/0.99  ------ Schedule UEQ
% 1.53/0.99  
% 1.53/0.99  ------ pure equality problem: resolution off 
% 1.53/0.99  
% 1.53/0.99  ------ Option_UEQ Time Limit: Unbounded
% 1.53/0.99  
% 1.53/0.99  
% 1.53/0.99  ------ 
% 1.53/0.99  Current options:
% 1.53/0.99  ------ 
% 1.53/0.99  
% 1.53/0.99  ------ Input Options
% 1.53/0.99  
% 1.53/0.99  --out_options                           all
% 1.53/0.99  --tptp_safe_out                         true
% 1.53/0.99  --problem_path                          ""
% 1.53/0.99  --include_path                          ""
% 1.53/0.99  --clausifier                            res/vclausify_rel
% 1.53/0.99  --clausifier_options                    --mode clausify
% 1.53/0.99  --stdin                                 false
% 1.53/0.99  --stats_out                             all
% 1.53/0.99  
% 1.53/0.99  ------ General Options
% 1.53/0.99  
% 1.53/0.99  --fof                                   false
% 1.53/0.99  --time_out_real                         305.
% 1.53/0.99  --time_out_virtual                      -1.
% 1.53/0.99  --symbol_type_check                     false
% 1.53/0.99  --clausify_out                          false
% 1.53/0.99  --sig_cnt_out                           false
% 1.53/0.99  --trig_cnt_out                          false
% 1.53/0.99  --trig_cnt_out_tolerance                1.
% 1.53/0.99  --trig_cnt_out_sk_spl                   false
% 1.53/0.99  --abstr_cl_out                          false
% 1.53/0.99  
% 1.53/0.99  ------ Global Options
% 1.53/0.99  
% 1.53/0.99  --schedule                              default
% 1.53/0.99  --add_important_lit                     false
% 1.53/0.99  --prop_solver_per_cl                    1000
% 1.53/0.99  --min_unsat_core                        false
% 1.53/0.99  --soft_assumptions                      false
% 1.53/0.99  --soft_lemma_size                       3
% 1.53/0.99  --prop_impl_unit_size                   0
% 1.53/0.99  --prop_impl_unit                        []
% 1.53/0.99  --share_sel_clauses                     true
% 1.53/0.99  --reset_solvers                         false
% 1.53/0.99  --bc_imp_inh                            [conj_cone]
% 1.53/0.99  --conj_cone_tolerance                   3.
% 1.53/0.99  --extra_neg_conj                        none
% 1.53/0.99  --large_theory_mode                     true
% 1.53/0.99  --prolific_symb_bound                   200
% 1.53/0.99  --lt_threshold                          2000
% 1.53/0.99  --clause_weak_htbl                      true
% 1.53/0.99  --gc_record_bc_elim                     false
% 1.53/0.99  
% 1.53/0.99  ------ Preprocessing Options
% 1.53/0.99  
% 1.53/0.99  --preprocessing_flag                    true
% 1.53/0.99  --time_out_prep_mult                    0.1
% 1.53/0.99  --splitting_mode                        input
% 1.53/0.99  --splitting_grd                         true
% 1.53/0.99  --splitting_cvd                         false
% 1.53/0.99  --splitting_cvd_svl                     false
% 1.53/0.99  --splitting_nvd                         32
% 1.53/0.99  --sub_typing                            true
% 1.53/0.99  --prep_gs_sim                           true
% 1.53/0.99  --prep_unflatten                        true
% 1.53/0.99  --prep_res_sim                          true
% 1.53/0.99  --prep_upred                            true
% 1.53/0.99  --prep_sem_filter                       exhaustive
% 1.53/0.99  --prep_sem_filter_out                   false
% 1.53/0.99  --pred_elim                             true
% 1.53/0.99  --res_sim_input                         true
% 1.53/0.99  --eq_ax_congr_red                       true
% 1.53/0.99  --pure_diseq_elim                       true
% 1.53/0.99  --brand_transform                       false
% 1.53/0.99  --non_eq_to_eq                          false
% 1.53/0.99  --prep_def_merge                        true
% 1.53/0.99  --prep_def_merge_prop_impl              false
% 1.53/0.99  --prep_def_merge_mbd                    true
% 1.53/0.99  --prep_def_merge_tr_red                 false
% 1.53/0.99  --prep_def_merge_tr_cl                  false
% 1.53/0.99  --smt_preprocessing                     true
% 1.53/0.99  --smt_ac_axioms                         fast
% 1.53/0.99  --preprocessed_out                      false
% 1.53/0.99  --preprocessed_stats                    false
% 1.53/0.99  
% 1.53/0.99  ------ Abstraction refinement Options
% 1.53/0.99  
% 1.53/0.99  --abstr_ref                             []
% 1.53/0.99  --abstr_ref_prep                        false
% 1.53/0.99  --abstr_ref_until_sat                   false
% 1.53/0.99  --abstr_ref_sig_restrict                funpre
% 1.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.53/0.99  --abstr_ref_under                       []
% 1.53/0.99  
% 1.53/0.99  ------ SAT Options
% 1.53/0.99  
% 1.53/0.99  --sat_mode                              false
% 1.53/0.99  --sat_fm_restart_options                ""
% 1.53/0.99  --sat_gr_def                            false
% 1.53/0.99  --sat_epr_types                         true
% 1.53/0.99  --sat_non_cyclic_types                  false
% 1.53/0.99  --sat_finite_models                     false
% 1.53/0.99  --sat_fm_lemmas                         false
% 1.53/0.99  --sat_fm_prep                           false
% 1.53/0.99  --sat_fm_uc_incr                        true
% 1.53/0.99  --sat_out_model                         small
% 1.53/0.99  --sat_out_clauses                       false
% 1.53/0.99  
% 1.53/0.99  ------ QBF Options
% 1.53/0.99  
% 1.53/0.99  --qbf_mode                              false
% 1.53/0.99  --qbf_elim_univ                         false
% 1.53/0.99  --qbf_dom_inst                          none
% 1.53/0.99  --qbf_dom_pre_inst                      false
% 1.53/0.99  --qbf_sk_in                             false
% 1.53/0.99  --qbf_pred_elim                         true
% 1.53/0.99  --qbf_split                             512
% 1.53/0.99  
% 1.53/0.99  ------ BMC1 Options
% 1.53/0.99  
% 1.53/0.99  --bmc1_incremental                      false
% 1.53/0.99  --bmc1_axioms                           reachable_all
% 1.53/0.99  --bmc1_min_bound                        0
% 1.53/0.99  --bmc1_max_bound                        -1
% 1.53/0.99  --bmc1_max_bound_default                -1
% 1.53/0.99  --bmc1_symbol_reachability              true
% 1.53/0.99  --bmc1_property_lemmas                  false
% 1.53/0.99  --bmc1_k_induction                      false
% 1.53/0.99  --bmc1_non_equiv_states                 false
% 1.53/0.99  --bmc1_deadlock                         false
% 1.53/0.99  --bmc1_ucm                              false
% 1.53/0.99  --bmc1_add_unsat_core                   none
% 1.53/0.99  --bmc1_unsat_core_children              false
% 1.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.53/0.99  --bmc1_out_stat                         full
% 1.53/0.99  --bmc1_ground_init                      false
% 1.53/0.99  --bmc1_pre_inst_next_state              false
% 1.53/0.99  --bmc1_pre_inst_state                   false
% 1.53/0.99  --bmc1_pre_inst_reach_state             false
% 1.53/0.99  --bmc1_out_unsat_core                   false
% 1.53/0.99  --bmc1_aig_witness_out                  false
% 1.53/0.99  --bmc1_verbose                          false
% 1.53/0.99  --bmc1_dump_clauses_tptp                false
% 1.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.53/0.99  --bmc1_dump_file                        -
% 1.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.53/0.99  --bmc1_ucm_extend_mode                  1
% 1.53/0.99  --bmc1_ucm_init_mode                    2
% 1.53/0.99  --bmc1_ucm_cone_mode                    none
% 1.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.53/0.99  --bmc1_ucm_relax_model                  4
% 1.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.53/0.99  --bmc1_ucm_layered_model                none
% 1.53/0.99  --bmc1_ucm_max_lemma_size               10
% 1.53/0.99  
% 1.53/0.99  ------ AIG Options
% 1.53/0.99  
% 1.53/0.99  --aig_mode                              false
% 1.53/0.99  
% 1.53/0.99  ------ Instantiation Options
% 1.53/0.99  
% 1.53/0.99  --instantiation_flag                    false
% 1.53/0.99  --inst_sos_flag                         false
% 1.53/0.99  --inst_sos_phase                        true
% 1.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.53/0.99  --inst_lit_sel_side                     num_symb
% 1.53/0.99  --inst_solver_per_active                1400
% 1.53/0.99  --inst_solver_calls_frac                1.
% 1.53/0.99  --inst_passive_queue_type               priority_queues
% 1.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.53/0.99  --inst_passive_queues_freq              [25;2]
% 1.53/0.99  --inst_dismatching                      true
% 1.53/0.99  --inst_eager_unprocessed_to_passive     true
% 1.53/0.99  --inst_prop_sim_given                   true
% 1.53/0.99  --inst_prop_sim_new                     false
% 1.53/0.99  --inst_subs_new                         false
% 1.53/0.99  --inst_eq_res_simp                      false
% 1.53/0.99  --inst_subs_given                       false
% 1.53/0.99  --inst_orphan_elimination               true
% 1.53/0.99  --inst_learning_loop_flag               true
% 1.53/0.99  --inst_learning_start                   3000
% 1.53/0.99  --inst_learning_factor                  2
% 1.53/0.99  --inst_start_prop_sim_after_learn       3
% 1.53/0.99  --inst_sel_renew                        solver
% 1.53/0.99  --inst_lit_activity_flag                true
% 1.53/0.99  --inst_restr_to_given                   false
% 1.53/0.99  --inst_activity_threshold               500
% 1.53/0.99  --inst_out_proof                        true
% 1.53/0.99  
% 1.53/0.99  ------ Resolution Options
% 1.53/0.99  
% 1.53/0.99  --resolution_flag                       false
% 1.53/0.99  --res_lit_sel                           adaptive
% 1.53/0.99  --res_lit_sel_side                      none
% 1.53/0.99  --res_ordering                          kbo
% 1.53/0.99  --res_to_prop_solver                    active
% 1.53/0.99  --res_prop_simpl_new                    false
% 1.53/0.99  --res_prop_simpl_given                  true
% 1.53/0.99  --res_passive_queue_type                priority_queues
% 1.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.53/0.99  --res_passive_queues_freq               [15;5]
% 1.53/0.99  --res_forward_subs                      full
% 1.53/0.99  --res_backward_subs                     full
% 1.53/0.99  --res_forward_subs_resolution           true
% 1.53/0.99  --res_backward_subs_resolution          true
% 1.53/0.99  --res_orphan_elimination                true
% 1.53/0.99  --res_time_limit                        2.
% 1.53/0.99  --res_out_proof                         true
% 1.53/0.99  
% 1.53/0.99  ------ Superposition Options
% 1.53/0.99  
% 1.53/0.99  --superposition_flag                    true
% 1.53/0.99  --sup_passive_queue_type                priority_queues
% 1.53/0.99  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.53/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.53/0.99  --demod_completeness_check              fast
% 1.53/0.99  --demod_use_ground                      true
% 1.53/0.99  --sup_to_prop_solver                    active
% 1.53/0.99  --sup_prop_simpl_new                    false
% 1.53/0.99  --sup_prop_simpl_given                  false
% 1.53/0.99  --sup_fun_splitting                     true
% 1.53/0.99  --sup_smt_interval                      10000
% 1.53/0.99  
% 1.53/0.99  ------ Superposition Simplification Setup
% 1.53/0.99  
% 1.53/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 1.53/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 1.53/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.99  --sup_full_triv                         [TrivRules]
% 1.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 1.53/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 1.53/0.99  --sup_immed_triv                        [TrivRules]
% 1.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 1.53/0.99  --sup_immed_bw_main                     []
% 1.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 1.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 1.53/0.99  --sup_input_bw                          [BwDemod;BwSubsumption]
% 1.53/0.99  
% 1.53/0.99  ------ Combination Options
% 1.53/0.99  
% 1.53/0.99  --comb_res_mult                         1
% 1.53/0.99  --comb_sup_mult                         1
% 1.53/0.99  --comb_inst_mult                        1000000
% 1.53/0.99  
% 1.53/0.99  ------ Debug Options
% 1.53/0.99  
% 1.53/0.99  --dbg_backtrace                         false
% 1.53/0.99  --dbg_dump_prop_clauses                 false
% 1.53/0.99  --dbg_dump_prop_clauses_file            -
% 1.53/0.99  --dbg_out_stat                          false
% 1.53/0.99  
% 1.53/0.99  
% 1.53/0.99  
% 1.53/0.99  
% 1.53/0.99  ------ Proving...
% 1.53/0.99  
% 1.53/0.99  
% 1.53/0.99  % SZS status Theorem for theBenchmark.p
% 1.53/0.99  
% 1.53/0.99   Resolution empty clause
% 1.53/0.99  
% 1.53/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.53/0.99  
% 1.53/0.99  fof(f9,axiom,(
% 1.53/0.99    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.99  
% 1.53/0.99  fof(f29,plain,(
% 1.53/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.53/0.99    inference(cnf_transformation,[],[f9])).
% 1.53/0.99  
% 1.53/0.99  fof(f4,axiom,(
% 1.53/0.99    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.99  
% 1.53/0.99  fof(f24,plain,(
% 1.53/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.53/0.99    inference(cnf_transformation,[],[f4])).
% 1.53/0.99  
% 1.53/0.99  fof(f2,axiom,(
% 1.53/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.99  
% 1.53/0.99  fof(f22,plain,(
% 1.53/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.53/0.99    inference(cnf_transformation,[],[f2])).
% 1.53/0.99  
% 1.53/0.99  fof(f12,axiom,(
% 1.53/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.99  
% 1.53/0.99  fof(f32,plain,(
% 1.53/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.53/0.99    inference(cnf_transformation,[],[f12])).
% 1.53/0.99  
% 1.53/0.99  fof(f38,plain,(
% 1.53/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.53/0.99    inference(definition_unfolding,[],[f24,f22,f32])).
% 1.53/0.99  
% 1.53/0.99  fof(f46,plain,(
% 1.53/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))) )),
% 1.53/0.99    inference(definition_unfolding,[],[f29,f22,f32,f38])).
% 1.53/0.99  
% 1.53/0.99  fof(f15,axiom,(
% 1.53/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.99  
% 1.53/0.99  fof(f35,plain,(
% 1.53/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.53/0.99    inference(cnf_transformation,[],[f15])).
% 1.53/0.99  
% 1.53/0.99  fof(f49,plain,(
% 1.53/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2))) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.53/0.99    inference(definition_unfolding,[],[f35,f38])).
% 1.53/0.99  
% 1.53/0.99  fof(f13,axiom,(
% 1.53/0.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.99  
% 1.53/0.99  fof(f33,plain,(
% 1.53/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.53/0.99    inference(cnf_transformation,[],[f13])).
% 1.53/0.99  
% 1.53/0.99  fof(f3,axiom,(
% 1.53/0.99    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 1.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.99  
% 1.53/0.99  fof(f23,plain,(
% 1.53/0.99    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.53/0.99    inference(cnf_transformation,[],[f3])).
% 1.53/0.99  
% 1.53/0.99  fof(f37,plain,(
% 1.53/0.99    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.53/0.99    inference(definition_unfolding,[],[f23,f22,f32,f32])).
% 1.53/0.99  
% 1.53/0.99  fof(f40,plain,(
% 1.53/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X0,X1,X2)) )),
% 1.53/0.99    inference(definition_unfolding,[],[f33,f37])).
% 1.53/0.99  
% 1.53/0.99  fof(f1,axiom,(
% 1.53/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.99  
% 1.53/0.99  fof(f21,plain,(
% 1.53/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.53/0.99    inference(cnf_transformation,[],[f1])).
% 1.53/0.99  
% 1.53/0.99  fof(f41,plain,(
% 1.53/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 1.53/0.99    inference(definition_unfolding,[],[f21,f22,f22])).
% 1.53/0.99  
% 1.53/0.99  fof(f5,axiom,(
% 1.53/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 1.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.99  
% 1.53/0.99  fof(f25,plain,(
% 1.53/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 1.53/0.99    inference(cnf_transformation,[],[f5])).
% 1.53/0.99  
% 1.53/0.99  fof(f42,plain,(
% 1.53/0.99    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1)))) )),
% 1.53/0.99    inference(definition_unfolding,[],[f25,f37,f37])).
% 1.53/0.99  
% 1.53/0.99  fof(f6,axiom,(
% 1.53/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 1.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.99  
% 1.53/0.99  fof(f26,plain,(
% 1.53/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 1.53/0.99    inference(cnf_transformation,[],[f6])).
% 1.53/0.99  
% 1.53/0.99  fof(f43,plain,(
% 1.53/0.99    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X0,X3),k4_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3)))) )),
% 1.53/0.99    inference(definition_unfolding,[],[f26,f37,f37])).
% 1.53/0.99  
% 1.53/0.99  fof(f16,conjecture,(
% 1.53/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 1.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.99  
% 1.53/0.99  fof(f17,negated_conjecture,(
% 1.53/0.99    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 1.53/0.99    inference(negated_conjecture,[],[f16])).
% 1.53/0.99  
% 1.53/0.99  fof(f18,plain,(
% 1.53/0.99    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 1.53/0.99    inference(ennf_transformation,[],[f17])).
% 1.53/0.99  
% 1.53/0.99  fof(f19,plain,(
% 1.53/0.99    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.53/0.99    introduced(choice_axiom,[])).
% 1.53/0.99  
% 1.53/0.99  fof(f20,plain,(
% 1.53/0.99    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).
% 1.53/0.99  
% 1.53/0.99  fof(f36,plain,(
% 1.53/0.99    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.53/0.99    inference(cnf_transformation,[],[f20])).
% 1.53/0.99  
% 1.53/0.99  fof(f50,plain,(
% 1.53/0.99    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))),
% 1.53/0.99    inference(definition_unfolding,[],[f36,f37,f37])).
% 1.53/0.99  
% 1.53/0.99  cnf(c_6,plain,
% 1.53/0.99      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2))) ),
% 1.53/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_30,plain,
% 1.53/0.99      ( k5_xboole_0(k1_enumset1(X0_38,X0_38,X1_38),k4_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X0_38,X1_38))) = k5_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k4_xboole_0(k1_enumset1(X3_38,X3_38,X4_38),k1_enumset1(X0_38,X1_38,X2_38))) ),
% 1.53/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_9,plain,
% 1.53/0.99      ( k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2))) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
% 1.53/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_28,plain,
% 1.53/0.99      ( k5_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k4_xboole_0(k1_enumset1(X3_38,X3_38,X4_38),k1_enumset1(X0_38,X1_38,X2_38))) = k4_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X4_38) ),
% 1.53/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_54,plain,
% 1.53/0.99      ( k5_xboole_0(k1_enumset1(X0_38,X0_38,X1_38),k4_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X0_38,X1_38))) = k4_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X4_38) ),
% 1.53/0.99      inference(light_normalisation,[status(thm)],[c_30,c_28]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_405,plain,
% 1.53/0.99      ( k4_enumset1(X0_38,X0_38,X1_38,X2_38,X2_38,X3_38) = k4_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38,X3_38) ),
% 1.53/0.99      inference(superposition,[status(thm)],[c_54,c_28]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_0,plain,
% 1.53/0.99      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X0,X1,X2) ),
% 1.53/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_36,plain,
% 1.53/0.99      ( k5_xboole_0(k1_enumset1(X0_38,X0_38,X0_38),k4_xboole_0(k1_enumset1(X1_38,X1_38,X2_38),k1_enumset1(X0_38,X0_38,X0_38))) = k1_enumset1(X0_38,X1_38,X2_38) ),
% 1.53/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_408,plain,
% 1.53/0.99      ( k4_enumset1(X0_38,X0_38,X0_38,X1_38,X1_38,X2_38) = k1_enumset1(X0_38,X1_38,X2_38) ),
% 1.53/0.99      inference(superposition,[status(thm)],[c_54,c_36]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_1,plain,
% 1.53/0.99      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 1.53/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_35,plain,
% 1.53/0.99      ( k5_xboole_0(X0_36,k4_xboole_0(X1_36,X0_36)) = k5_xboole_0(X1_36,k4_xboole_0(X0_36,X1_36)) ),
% 1.53/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_146,plain,
% 1.53/0.99      ( k5_xboole_0(k1_enumset1(X0_38,X0_38,X1_38),k4_xboole_0(k1_enumset1(X2_38,X2_38,X2_38),k1_enumset1(X0_38,X0_38,X1_38))) = k1_enumset1(X2_38,X0_38,X1_38) ),
% 1.53/0.99      inference(superposition,[status(thm)],[c_35,c_36]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_181,plain,
% 1.53/0.99      ( k4_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38,X2_38) = k1_enumset1(X2_38,X0_38,X1_38) ),
% 1.53/0.99      inference(superposition,[status(thm)],[c_146,c_28]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_2,plain,
% 1.53/0.99      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1))) ),
% 1.53/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_34,plain,
% 1.53/0.99      ( k5_xboole_0(k1_enumset1(X0_38,X0_38,X1_38),k4_xboole_0(k1_enumset1(X2_38,X2_38,X3_38),k1_enumset1(X0_38,X0_38,X1_38))) = k5_xboole_0(k1_enumset1(X0_38,X0_38,X1_38),k4_xboole_0(k1_enumset1(X3_38,X3_38,X2_38),k1_enumset1(X0_38,X0_38,X1_38))) ),
% 1.53/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_52,plain,
% 1.53/0.99      ( k4_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38,X3_38) = k4_enumset1(X0_38,X0_38,X0_38,X1_38,X3_38,X2_38) ),
% 1.53/0.99      inference(demodulation,[status(thm)],[c_34,c_28]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_3,plain,
% 1.53/0.99      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X0,X3),k4_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X3))) ),
% 1.53/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_33,plain,
% 1.53/0.99      ( k5_xboole_0(k1_enumset1(X0_38,X0_38,X1_38),k4_xboole_0(k1_enumset1(X2_38,X2_38,X3_38),k1_enumset1(X0_38,X0_38,X1_38))) = k5_xboole_0(k1_enumset1(X0_38,X0_38,X3_38),k4_xboole_0(k1_enumset1(X2_38,X2_38,X1_38),k1_enumset1(X0_38,X0_38,X3_38))) ),
% 1.53/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_53,plain,
% 1.53/0.99      ( k4_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38,X3_38) = k4_enumset1(X0_38,X0_38,X0_38,X3_38,X2_38,X1_38) ),
% 1.53/0.99      inference(demodulation,[status(thm)],[c_33,c_28]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_62,plain,
% 1.53/0.99      ( k4_enumset1(X0_38,X0_38,X0_38,X1_38,X2_38,X3_38) = k4_enumset1(X0_38,X0_38,X0_38,X3_38,X1_38,X2_38) ),
% 1.53/0.99      inference(superposition,[status(thm)],[c_52,c_53]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_206,plain,
% 1.53/0.99      ( k4_enumset1(X0_38,X0_38,X0_38,X1_38,X1_38,X2_38) = k1_enumset1(X1_38,X0_38,X2_38) ),
% 1.53/0.99      inference(superposition,[status(thm)],[c_181,c_62]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_433,plain,
% 1.53/0.99      ( k1_enumset1(X0_38,X1_38,X2_38) = k1_enumset1(X1_38,X0_38,X2_38) ),
% 1.53/0.99      inference(superposition,[status(thm)],[c_408,c_206]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_573,plain,
% 1.53/0.99      ( k5_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k4_xboole_0(k1_enumset1(X3_38,X3_38,X4_38),k1_enumset1(X0_38,X1_38,X2_38))) = k4_enumset1(X1_38,X1_38,X0_38,X2_38,X3_38,X4_38) ),
% 1.53/0.99      inference(superposition,[status(thm)],[c_433,c_28]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_2848,plain,
% 1.53/0.99      ( k4_enumset1(X0_38,X0_38,X1_38,X2_38,X3_38,X4_38) = k4_enumset1(X1_38,X1_38,X0_38,X2_38,X3_38,X4_38) ),
% 1.53/0.99      inference(superposition,[status(thm)],[c_573,c_28]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_10,negated_conjecture,
% 1.53/0.99      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) ),
% 1.53/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_27,negated_conjecture,
% 1.53/0.99      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))) ),
% 1.53/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_56,plain,
% 1.53/0.99      ( k4_enumset1(sK1,sK1,sK0,sK2,sK2,sK3) != k4_enumset1(sK0,sK0,sK1,sK2,sK2,sK3) ),
% 1.53/0.99      inference(demodulation,[status(thm)],[c_27,c_54]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_440,plain,
% 1.53/0.99      ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK1,sK1,sK0,sK2,sK2,sK3) ),
% 1.53/0.99      inference(demodulation,[status(thm)],[c_405,c_56]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_2862,plain,
% 1.53/0.99      ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK1,sK2,sK2,sK3) ),
% 1.53/0.99      inference(demodulation,[status(thm)],[c_2848,c_440]) ).
% 1.53/0.99  
% 1.53/0.99  cnf(c_2937,plain,
% 1.53/0.99      ( $false ),
% 1.53/0.99      inference(superposition,[status(thm)],[c_405,c_2862]) ).
% 1.53/0.99  
% 1.53/0.99  
% 1.53/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.53/0.99  
% 1.53/0.99  ------                               Statistics
% 1.53/0.99  
% 1.53/0.99  ------ General
% 1.53/0.99  
% 1.53/0.99  abstr_ref_over_cycles:                  0
% 1.53/0.99  abstr_ref_under_cycles:                 0
% 1.53/0.99  gc_basic_clause_elim:                   0
% 1.53/0.99  forced_gc_time:                         0
% 1.53/0.99  parsing_time:                           0.007
% 1.53/0.99  unif_index_cands_time:                  0.
% 1.53/0.99  unif_index_add_time:                    0.
% 1.53/0.99  orderings_time:                         0.
% 1.53/0.99  out_proof_time:                         0.008
% 1.53/0.99  total_time:                             0.11
% 1.53/0.99  num_of_symbols:                         39
% 1.53/0.99  num_of_terms:                           2285
% 1.53/0.99  
% 1.53/0.99  ------ Preprocessing
% 1.53/0.99  
% 1.53/0.99  num_of_splits:                          0
% 1.53/0.99  num_of_split_atoms:                     0
% 1.53/0.99  num_of_reused_defs:                     0
% 1.53/0.99  num_eq_ax_congr_red:                    21
% 1.53/0.99  num_of_sem_filtered_clauses:            0
% 1.53/0.99  num_of_subtypes:                        3
% 1.53/0.99  monotx_restored_types:                  0
% 1.53/0.99  sat_num_of_epr_types:                   0
% 1.53/0.99  sat_num_of_non_cyclic_types:            0
% 1.53/0.99  sat_guarded_non_collapsed_types:        0
% 1.53/0.99  num_pure_diseq_elim:                    0
% 1.53/0.99  simp_replaced_by:                       0
% 1.53/0.99  res_preprocessed:                       35
% 1.53/0.99  prep_upred:                             0
% 1.53/0.99  prep_unflattend:                        0
% 1.53/0.99  smt_new_axioms:                         0
% 1.53/0.99  pred_elim_cands:                        0
% 1.53/0.99  pred_elim:                              0
% 1.53/0.99  pred_elim_cl:                           0
% 1.53/0.99  pred_elim_cycles:                       0
% 1.53/0.99  merged_defs:                            0
% 1.53/0.99  merged_defs_ncl:                        0
% 1.53/0.99  bin_hyper_res:                          0
% 1.53/0.99  prep_cycles:                            3
% 1.53/0.99  pred_elim_time:                         0.
% 1.53/0.99  splitting_time:                         0.
% 1.53/0.99  sem_filter_time:                        0.
% 1.53/0.99  monotx_time:                            0.
% 1.53/0.99  subtype_inf_time:                       0.
% 1.53/0.99  
% 1.53/0.99  ------ Problem properties
% 1.53/0.99  
% 1.53/0.99  clauses:                                10
% 1.53/0.99  conjectures:                            1
% 1.53/0.99  epr:                                    0
% 1.53/0.99  horn:                                   10
% 1.53/0.99  ground:                                 1
% 1.53/0.99  unary:                                  10
% 1.53/0.99  binary:                                 0
% 1.53/0.99  lits:                                   10
% 1.53/0.99  lits_eq:                                10
% 1.53/0.99  fd_pure:                                0
% 1.53/0.99  fd_pseudo:                              0
% 1.53/0.99  fd_cond:                                0
% 1.53/0.99  fd_pseudo_cond:                         0
% 1.53/0.99  ac_symbols:                             0
% 1.53/0.99  
% 1.53/0.99  ------ Propositional Solver
% 1.53/0.99  
% 1.53/0.99  prop_solver_calls:                      17
% 1.53/0.99  prop_fast_solver_calls:                 82
% 1.53/0.99  smt_solver_calls:                       0
% 1.53/0.99  smt_fast_solver_calls:                  0
% 1.53/0.99  prop_num_of_clauses:                    110
% 1.53/0.99  prop_preprocess_simplified:             494
% 1.53/0.99  prop_fo_subsumed:                       0
% 1.53/0.99  prop_solver_time:                       0.
% 1.53/0.99  smt_solver_time:                        0.
% 1.53/0.99  smt_fast_solver_time:                   0.
% 1.53/0.99  prop_fast_solver_time:                  0.
% 1.53/0.99  prop_unsat_core_time:                   0.
% 1.53/0.99  
% 1.53/0.99  ------ QBF
% 1.53/0.99  
% 1.53/0.99  qbf_q_res:                              0
% 1.53/0.99  qbf_num_tautologies:                    0
% 1.53/0.99  qbf_prep_cycles:                        0
% 1.53/0.99  
% 1.53/0.99  ------ BMC1
% 1.53/0.99  
% 1.53/0.99  bmc1_current_bound:                     -1
% 1.53/0.99  bmc1_last_solved_bound:                 -1
% 1.53/0.99  bmc1_unsat_core_size:                   -1
% 1.53/0.99  bmc1_unsat_core_parents_size:           -1
% 1.53/0.99  bmc1_merge_next_fun:                    0
% 1.53/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.53/0.99  
% 1.53/0.99  ------ Instantiation
% 1.53/0.99  
% 1.53/0.99  inst_num_of_clauses:                    0
% 1.53/0.99  inst_num_in_passive:                    0
% 1.53/0.99  inst_num_in_active:                     0
% 1.53/0.99  inst_num_in_unprocessed:                0
% 1.53/0.99  inst_num_of_loops:                      0
% 1.53/0.99  inst_num_of_learning_restarts:          0
% 1.53/0.99  inst_num_moves_active_passive:          0
% 1.53/0.99  inst_lit_activity:                      0
% 1.53/0.99  inst_lit_activity_moves:                0
% 1.53/0.99  inst_num_tautologies:                   0
% 1.53/0.99  inst_num_prop_implied:                  0
% 1.53/0.99  inst_num_existing_simplified:           0
% 1.53/0.99  inst_num_eq_res_simplified:             0
% 1.53/0.99  inst_num_child_elim:                    0
% 1.53/0.99  inst_num_of_dismatching_blockings:      0
% 1.53/0.99  inst_num_of_non_proper_insts:           0
% 1.53/0.99  inst_num_of_duplicates:                 0
% 1.53/0.99  inst_inst_num_from_inst_to_res:         0
% 1.53/0.99  inst_dismatching_checking_time:         0.
% 1.53/0.99  
% 1.53/0.99  ------ Resolution
% 1.53/0.99  
% 1.53/0.99  res_num_of_clauses:                     0
% 1.53/0.99  res_num_in_passive:                     0
% 1.53/0.99  res_num_in_active:                      0
% 1.53/0.99  res_num_of_loops:                       38
% 1.53/0.99  res_forward_subset_subsumed:            0
% 1.53/0.99  res_backward_subset_subsumed:           0
% 1.53/0.99  res_forward_subsumed:                   0
% 1.53/0.99  res_backward_subsumed:                  0
% 1.53/0.99  res_forward_subsumption_resolution:     0
% 1.53/0.99  res_backward_subsumption_resolution:    0
% 1.53/0.99  res_clause_to_clause_subsumption:       7014
% 1.53/0.99  res_orphan_elimination:                 0
% 1.53/0.99  res_tautology_del:                      1
% 1.53/0.99  res_num_eq_res_simplified:              0
% 1.53/0.99  res_num_sel_changes:                    0
% 1.53/0.99  res_moves_from_active_to_pass:          0
% 1.53/0.99  
% 1.53/0.99  ------ Superposition
% 1.53/0.99  
% 1.53/0.99  sup_time_total:                         0.
% 1.53/0.99  sup_time_generating:                    0.
% 1.53/0.99  sup_time_sim_full:                      0.
% 1.53/0.99  sup_time_sim_immed:                     0.
% 1.53/0.99  
% 1.53/0.99  sup_num_of_clauses:                     377
% 1.53/0.99  sup_num_in_active:                      64
% 1.53/0.99  sup_num_in_passive:                     313
% 1.53/0.99  sup_num_of_loops:                       65
% 1.53/0.99  sup_fw_superposition:                   1492
% 1.53/0.99  sup_bw_superposition:                   1297
% 1.53/0.99  sup_immediate_simplified:               116
% 1.53/0.99  sup_given_eliminated:                   0
% 1.53/0.99  comparisons_done:                       0
% 1.53/0.99  comparisons_avoided:                    0
% 1.53/0.99  
% 1.53/0.99  ------ Simplifications
% 1.53/0.99  
% 1.53/0.99  
% 1.53/0.99  sim_fw_subset_subsumed:                 0
% 1.53/0.99  sim_bw_subset_subsumed:                 0
% 1.53/0.99  sim_fw_subsumed:                        33
% 1.53/0.99  sim_bw_subsumed:                        5
% 1.53/0.99  sim_fw_subsumption_res:                 0
% 1.53/0.99  sim_bw_subsumption_res:                 0
% 1.53/0.99  sim_tautology_del:                      0
% 1.53/0.99  sim_eq_tautology_del:                   5
% 1.53/0.99  sim_eq_res_simp:                        0
% 1.53/0.99  sim_fw_demodulated:                     49
% 1.53/0.99  sim_bw_demodulated:                     4
% 1.53/0.99  sim_light_normalised:                   38
% 1.53/0.99  sim_joinable_taut:                      0
% 1.53/0.99  sim_joinable_simp:                      0
% 1.53/0.99  sim_ac_normalised:                      0
% 1.53/0.99  sim_smt_subsumption:                    0
% 1.53/0.99  
%------------------------------------------------------------------------------
