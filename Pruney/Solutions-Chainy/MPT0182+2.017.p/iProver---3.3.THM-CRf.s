%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:42 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 235 expanded)
%              Number of clauses        :   22 (  33 expanded)
%              Number of leaves         :   14 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :   63 ( 236 expanded)
%              Number of equality atoms :   62 ( 235 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f25,f39,f30])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f40,f43])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f39,f39])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k5_xboole_0(k2_tarski(X6,X6),k3_xboole_0(k2_tarski(X6,X6),k4_enumset1(X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f26,f39,f30])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k5_xboole_0(k2_tarski(X5,X5),k3_xboole_0(k2_tarski(X5,X5),k4_enumset1(X0,X0,X1,X2,X3,X4)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X2,X1),k3_xboole_0(k2_tarski(X2,X1),k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f37,f40,f40])).

fof(f17,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(negated_conjecture,[],[f17])).

fof(f19,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) ),
    inference(ennf_transformation,[],[f18])).

fof(f20,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f38,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK0,sK2),k3_xboole_0(k2_tarski(sK0,sK2),k2_tarski(sK1,sK1)))) ),
    inference(definition_unfolding,[],[f38,f40,f40])).

cnf(c_5,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,plain,
    ( k5_xboole_0(k2_tarski(X0_36,X0_36),k5_xboole_0(k2_tarski(X1_36,X2_36),k3_xboole_0(k2_tarski(X1_36,X2_36),k2_tarski(X0_36,X0_36)))) = k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_27,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) = k5_xboole_0(X1_35,k5_xboole_0(X0_35,k3_xboole_0(X0_35,X1_35))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_199,plain,
    ( k5_xboole_0(k2_tarski(X0_36,X1_36),k5_xboole_0(k2_tarski(X2_36,X2_36),k3_xboole_0(k2_tarski(X2_36,X2_36),k2_tarski(X0_36,X1_36)))) = k4_enumset1(X2_36,X2_36,X2_36,X2_36,X0_36,X1_36) ),
    inference(superposition,[status(thm)],[c_24,c_27])).

cnf(c_0,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_29,plain,
    ( k5_xboole_0(k2_tarski(X0_36,X0_36),k5_xboole_0(k2_tarski(X0_36,X1_36),k3_xboole_0(k2_tarski(X0_36,X1_36),k2_tarski(X0_36,X0_36)))) = k2_tarski(X0_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_201,plain,
    ( k4_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36) = k2_tarski(X0_36,X1_36) ),
    inference(superposition,[status(thm)],[c_24,c_29])).

cnf(c_1,plain,
    ( k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k5_xboole_0(k2_tarski(X5,X5),k3_xboole_0(k2_tarski(X5,X5),k4_enumset1(X0,X0,X1,X2,X3,X4)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_28,plain,
    ( k5_xboole_0(k4_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36),k5_xboole_0(k2_tarski(X5_36,X5_36),k3_xboole_0(k2_tarski(X5_36,X5_36),k4_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36)))) = k4_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_399,plain,
    ( k5_xboole_0(k2_tarski(X0_36,X1_36),k5_xboole_0(k2_tarski(X2_36,X2_36),k3_xboole_0(k2_tarski(X2_36,X2_36),k2_tarski(X0_36,X1_36)))) = k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_201,c_28])).

cnf(c_853,plain,
    ( k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k4_enumset1(X2_36,X2_36,X2_36,X2_36,X0_36,X1_36) ),
    inference(superposition,[status(thm)],[c_199,c_399])).

cnf(c_7,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X2,X1),k3_xboole_0(k2_tarski(X2,X1),k2_tarski(X0,X0)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,plain,
    ( k5_xboole_0(k2_tarski(X0_36,X0_36),k5_xboole_0(k2_tarski(X1_36,X2_36),k3_xboole_0(k2_tarski(X1_36,X2_36),k2_tarski(X0_36,X0_36)))) = k5_xboole_0(k2_tarski(X0_36,X0_36),k5_xboole_0(k2_tarski(X2_36,X1_36),k3_xboole_0(k2_tarski(X2_36,X1_36),k2_tarski(X0_36,X0_36)))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_52,plain,
    ( k5_xboole_0(k2_tarski(X0_36,X0_36),k5_xboole_0(k2_tarski(X1_36,X2_36),k3_xboole_0(k2_tarski(X1_36,X2_36),k2_tarski(X0_36,X0_36)))) = k4_enumset1(X0_36,X0_36,X0_36,X0_36,X2_36,X1_36) ),
    inference(light_normalisation,[status(thm)],[c_22,c_24])).

cnf(c_260,plain,
    ( k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k4_enumset1(X0_36,X0_36,X0_36,X0_36,X2_36,X1_36) ),
    inference(superposition,[status(thm)],[c_52,c_24])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK0,sK2),k3_xboole_0(k2_tarski(sK0,sK2),k2_tarski(sK1,sK1)))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,negated_conjecture,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK0,sK2),k3_xboole_0(k2_tarski(sK0,sK2),k2_tarski(sK1,sK1)))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_55,plain,
    ( k4_enumset1(sK1,sK1,sK1,sK1,sK2,sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_21,c_52])).

cnf(c_531,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK1,sK1,sK1,sK1,sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_260,c_55])).

cnf(c_2032,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_853,c_531])).

cnf(c_2036,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2032])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:26:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.60/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.60/1.00  
% 2.60/1.00  ------  iProver source info
% 2.60/1.00  
% 2.60/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.60/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.60/1.00  git: non_committed_changes: false
% 2.60/1.00  git: last_make_outside_of_git: false
% 2.60/1.00  
% 2.60/1.00  ------ 
% 2.60/1.00  ------ Parsing...
% 2.60/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.60/1.00  ------ Proving...
% 2.60/1.00  ------ Problem Properties 
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  clauses                                 9
% 2.60/1.00  conjectures                             1
% 2.60/1.00  EPR                                     0
% 2.60/1.00  Horn                                    9
% 2.60/1.00  unary                                   9
% 2.60/1.00  binary                                  0
% 2.60/1.00  lits                                    9
% 2.60/1.00  lits eq                                 9
% 2.60/1.00  fd_pure                                 0
% 2.60/1.00  fd_pseudo                               0
% 2.60/1.00  fd_cond                                 0
% 2.60/1.00  fd_pseudo_cond                          0
% 2.60/1.00  AC symbols                              0
% 2.60/1.00  
% 2.60/1.00  ------ Input Options Time Limit: Unbounded
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  ------ 
% 2.60/1.00  Current options:
% 2.60/1.00  ------ 
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  ------ Proving...
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  % SZS status Theorem for theBenchmark.p
% 2.60/1.00  
% 2.60/1.00   Resolution empty clause
% 2.60/1.00  
% 2.60/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  fof(f11,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f32,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f11])).
% 2.60/1.00  
% 2.60/1.00  fof(f4,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f25,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f4])).
% 2.60/1.00  
% 2.60/1.00  fof(f3,axiom,(
% 2.60/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f24,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.60/1.00    inference(cnf_transformation,[],[f3])).
% 2.60/1.00  
% 2.60/1.00  fof(f2,axiom,(
% 2.60/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f23,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.60/1.00    inference(cnf_transformation,[],[f2])).
% 2.60/1.00  
% 2.60/1.00  fof(f39,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.60/1.00    inference(definition_unfolding,[],[f24,f23])).
% 2.60/1.00  
% 2.60/1.00  fof(f9,axiom,(
% 2.60/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f30,plain,(
% 2.60/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f9])).
% 2.60/1.00  
% 2.60/1.00  fof(f40,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f25,f39,f30])).
% 2.60/1.00  
% 2.60/1.00  fof(f12,axiom,(
% 2.60/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f33,plain,(
% 2.60/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f12])).
% 2.60/1.00  
% 2.60/1.00  fof(f13,axiom,(
% 2.60/1.00    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f34,plain,(
% 2.60/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f13])).
% 2.60/1.00  
% 2.60/1.00  fof(f43,plain,(
% 2.60/1.00    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f33,f34])).
% 2.60/1.00  
% 2.60/1.00  fof(f49,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f32,f40,f43])).
% 2.60/1.00  
% 2.60/1.00  fof(f1,axiom,(
% 2.60/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f22,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f1])).
% 2.60/1.00  
% 2.60/1.00  fof(f46,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.60/1.00    inference(definition_unfolding,[],[f22,f39,f39])).
% 2.60/1.00  
% 2.60/1.00  fof(f10,axiom,(
% 2.60/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f31,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f10])).
% 2.60/1.00  
% 2.60/1.00  fof(f44,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f31,f40])).
% 2.60/1.00  
% 2.60/1.00  fof(f14,axiom,(
% 2.60/1.00    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f35,plain,(
% 2.60/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f14])).
% 2.60/1.00  
% 2.60/1.00  fof(f5,axiom,(
% 2.60/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f26,plain,(
% 2.60/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f5])).
% 2.60/1.00  
% 2.60/1.00  fof(f41,plain,(
% 2.60/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k5_xboole_0(k2_tarski(X6,X6),k3_xboole_0(k2_tarski(X6,X6),k4_enumset1(X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f26,f39,f30])).
% 2.60/1.00  
% 2.60/1.00  fof(f45,plain,(
% 2.60/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k5_xboole_0(k2_tarski(X5,X5),k3_xboole_0(k2_tarski(X5,X5),k4_enumset1(X0,X0,X1,X2,X3,X4)))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f35,f41])).
% 2.60/1.00  
% 2.60/1.00  fof(f16,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f37,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f16])).
% 2.60/1.00  
% 2.60/1.00  fof(f51,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X2,X1),k3_xboole_0(k2_tarski(X2,X1),k2_tarski(X0,X0))))) )),
% 2.60/1.00    inference(definition_unfolding,[],[f37,f40,f40])).
% 2.60/1.00  
% 2.60/1.00  fof(f17,conjecture,(
% 2.60/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f18,negated_conjecture,(
% 2.60/1.00    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 2.60/1.00    inference(negated_conjecture,[],[f17])).
% 2.60/1.00  
% 2.60/1.00  fof(f19,plain,(
% 2.60/1.00    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)),
% 2.60/1.00    inference(ennf_transformation,[],[f18])).
% 2.60/1.00  
% 2.60/1.00  fof(f20,plain,(
% 2.60/1.00    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f21,plain,(
% 2.60/1.00    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 2.60/1.00  
% 2.60/1.00  fof(f38,plain,(
% 2.60/1.00    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 2.60/1.00    inference(cnf_transformation,[],[f21])).
% 2.60/1.00  
% 2.60/1.00  fof(f52,plain,(
% 2.60/1.00    k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK0,sK2),k3_xboole_0(k2_tarski(sK0,sK2),k2_tarski(sK1,sK1))))),
% 2.60/1.00    inference(definition_unfolding,[],[f38,f40,f40])).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5,plain,
% 2.60/1.00      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
% 2.60/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_24,plain,
% 2.60/1.00      ( k5_xboole_0(k2_tarski(X0_36,X0_36),k5_xboole_0(k2_tarski(X1_36,X2_36),k3_xboole_0(k2_tarski(X1_36,X2_36),k2_tarski(X0_36,X0_36)))) = k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) ),
% 2.60/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2,plain,
% 2.60/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 2.60/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_27,plain,
% 2.60/1.00      ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) = k5_xboole_0(X1_35,k5_xboole_0(X0_35,k3_xboole_0(X0_35,X1_35))) ),
% 2.60/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_199,plain,
% 2.60/1.00      ( k5_xboole_0(k2_tarski(X0_36,X1_36),k5_xboole_0(k2_tarski(X2_36,X2_36),k3_xboole_0(k2_tarski(X2_36,X2_36),k2_tarski(X0_36,X1_36)))) = k4_enumset1(X2_36,X2_36,X2_36,X2_36,X0_36,X1_36) ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_24,c_27]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_0,plain,
% 2.60/1.00      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_29,plain,
% 2.60/1.00      ( k5_xboole_0(k2_tarski(X0_36,X0_36),k5_xboole_0(k2_tarski(X0_36,X1_36),k3_xboole_0(k2_tarski(X0_36,X1_36),k2_tarski(X0_36,X0_36)))) = k2_tarski(X0_36,X1_36) ),
% 2.60/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_201,plain,
% 2.60/1.00      ( k4_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36) = k2_tarski(X0_36,X1_36) ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_24,c_29]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1,plain,
% 2.60/1.00      ( k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k5_xboole_0(k2_tarski(X5,X5),k3_xboole_0(k2_tarski(X5,X5),k4_enumset1(X0,X0,X1,X2,X3,X4)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 2.60/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_28,plain,
% 2.60/1.00      ( k5_xboole_0(k4_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36),k5_xboole_0(k2_tarski(X5_36,X5_36),k3_xboole_0(k2_tarski(X5_36,X5_36),k4_enumset1(X0_36,X0_36,X1_36,X2_36,X3_36,X4_36)))) = k4_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36) ),
% 2.60/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_399,plain,
% 2.60/1.00      ( k5_xboole_0(k2_tarski(X0_36,X1_36),k5_xboole_0(k2_tarski(X2_36,X2_36),k3_xboole_0(k2_tarski(X2_36,X2_36),k2_tarski(X0_36,X1_36)))) = k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_201,c_28]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_853,plain,
% 2.60/1.00      ( k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k4_enumset1(X2_36,X2_36,X2_36,X2_36,X0_36,X1_36) ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_199,c_399]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_7,plain,
% 2.60/1.00      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X2,X1),k3_xboole_0(k2_tarski(X2,X1),k2_tarski(X0,X0)))) ),
% 2.60/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_22,plain,
% 2.60/1.00      ( k5_xboole_0(k2_tarski(X0_36,X0_36),k5_xboole_0(k2_tarski(X1_36,X2_36),k3_xboole_0(k2_tarski(X1_36,X2_36),k2_tarski(X0_36,X0_36)))) = k5_xboole_0(k2_tarski(X0_36,X0_36),k5_xboole_0(k2_tarski(X2_36,X1_36),k3_xboole_0(k2_tarski(X2_36,X1_36),k2_tarski(X0_36,X0_36)))) ),
% 2.60/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_52,plain,
% 2.60/1.00      ( k5_xboole_0(k2_tarski(X0_36,X0_36),k5_xboole_0(k2_tarski(X1_36,X2_36),k3_xboole_0(k2_tarski(X1_36,X2_36),k2_tarski(X0_36,X0_36)))) = k4_enumset1(X0_36,X0_36,X0_36,X0_36,X2_36,X1_36) ),
% 2.60/1.00      inference(light_normalisation,[status(thm)],[c_22,c_24]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_260,plain,
% 2.60/1.00      ( k4_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k4_enumset1(X0_36,X0_36,X0_36,X0_36,X2_36,X1_36) ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_52,c_24]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_8,negated_conjecture,
% 2.60/1.00      ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK0,sK2),k3_xboole_0(k2_tarski(sK0,sK2),k2_tarski(sK1,sK1)))) ),
% 2.60/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_21,negated_conjecture,
% 2.60/1.00      ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK0,sK2),k3_xboole_0(k2_tarski(sK0,sK2),k2_tarski(sK1,sK1)))) ),
% 2.60/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_55,plain,
% 2.60/1.00      ( k4_enumset1(sK1,sK1,sK1,sK1,sK2,sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 2.60/1.00      inference(demodulation,[status(thm)],[c_21,c_52]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_531,plain,
% 2.60/1.00      ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK1,sK1,sK1,sK1,sK2,sK0) ),
% 2.60/1.00      inference(demodulation,[status(thm)],[c_260,c_55]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2032,plain,
% 2.60/1.00      ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 2.60/1.00      inference(demodulation,[status(thm)],[c_853,c_531]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2036,plain,
% 2.60/1.00      ( $false ),
% 2.60/1.00      inference(equality_resolution_simp,[status(thm)],[c_2032]) ).
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  ------                               Statistics
% 2.60/1.00  
% 2.60/1.00  ------ Selected
% 2.60/1.00  
% 2.60/1.00  total_time:                             0.115
% 2.60/1.00  
%------------------------------------------------------------------------------
