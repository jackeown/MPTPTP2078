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
% DateTime   : Thu Dec  3 11:27:17 EST 2020

% Result     : Theorem 0.70s
% Output     : CNFRefutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 148 expanded)
%              Number of clauses        :   17 (  27 expanded)
%              Number of leaves         :   10 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   48 ( 149 expanded)
%              Number of equality atoms :   47 ( 148 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f16,f14])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k2_tarski(X4,X5),k1_tarski(X3))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f15,f14,f23,f23])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f18,f14,f23])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f21,f24,f26])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f17,f14,f23])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))),k4_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f20,f25,f26])).

fof(f9,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f10])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k3_enumset1(X0,X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f22,plain,(
    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))),k4_xboole_0(k2_tarski(sK1,sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f22,f23,f26])).

cnf(c_0,plain,
    ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_16,plain,
    ( k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X0_37,X1_37),k1_tarski(X0_37))) = k2_tarski(X0_37,X1_37) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_14,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X0_37,X1_37),k1_tarski(X0_37))),k4_xboole_0(k5_xboole_0(k1_tarski(X2_37),k4_xboole_0(k2_tarski(X3_37,X4_37),k1_tarski(X2_37))),k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X0_37,X1_37),k1_tarski(X0_37))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k1_tarski(X0_37))),k4_xboole_0(k2_tarski(X3_37,X4_37),k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k1_tarski(X0_37))))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_31,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k1_tarski(X0_37))),k4_xboole_0(k2_tarski(X3_37,X4_37),k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k1_tarski(X0_37))))) = k5_xboole_0(k2_tarski(X0_37,X1_37),k4_xboole_0(k5_xboole_0(k1_tarski(X2_37),k4_xboole_0(k2_tarski(X3_37,X4_37),k1_tarski(X2_37))),k2_tarski(X0_37,X1_37))) ),
    inference(light_normalisation,[status(thm)],[c_14,c_16])).

cnf(c_36,plain,
    ( k5_xboole_0(k2_tarski(X0_37,X0_37),k4_xboole_0(k5_xboole_0(k1_tarski(X1_37),k4_xboole_0(k2_tarski(X2_37,X3_37),k1_tarski(X1_37))),k2_tarski(X0_37,X0_37))) = k5_xboole_0(k2_tarski(X0_37,X1_37),k4_xboole_0(k2_tarski(X2_37,X3_37),k2_tarski(X0_37,X1_37))) ),
    inference(superposition,[status(thm)],[c_16,c_31])).

cnf(c_39,plain,
    ( k5_xboole_0(k2_tarski(X0_37,X0_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k2_tarski(X0_37,X0_37))) = k5_xboole_0(k2_tarski(X0_37,X1_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k2_tarski(X0_37,X1_37))) ),
    inference(superposition,[status(thm)],[c_16,c_36])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))),k4_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_15,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X0_37,X1_37),k1_tarski(X0_37))),k4_xboole_0(k2_tarski(X2_37,X3_37),k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X0_37,X1_37),k1_tarski(X0_37))))) = k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k5_xboole_0(k1_tarski(X1_37),k4_xboole_0(k2_tarski(X2_37,X3_37),k1_tarski(X1_37))),k1_tarski(X0_37))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_30,plain,
    ( k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k5_xboole_0(k1_tarski(X1_37),k4_xboole_0(k2_tarski(X2_37,X3_37),k1_tarski(X1_37))),k1_tarski(X0_37))) = k5_xboole_0(k2_tarski(X0_37,X1_37),k4_xboole_0(k2_tarski(X2_37,X3_37),k2_tarski(X0_37,X1_37))) ),
    inference(light_normalisation,[status(thm)],[c_15,c_16])).

cnf(c_33,plain,
    ( k5_xboole_0(k2_tarski(X0_37,X1_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k2_tarski(X0_37,X1_37))) = k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k1_tarski(X0_37))) ),
    inference(superposition,[status(thm)],[c_16,c_30])).

cnf(c_40,plain,
    ( k5_xboole_0(k2_tarski(X0_37,X0_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k2_tarski(X0_37,X0_37))) = k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k1_tarski(X0_37))) ),
    inference(light_normalisation,[status(thm)],[c_39,c_33])).

cnf(c_3,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))),k4_xboole_0(k2_tarski(sK1,sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))),k4_xboole_0(k2_tarski(sK1,sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_29,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) ),
    inference(demodulation,[status(thm)],[c_13,c_16])).

cnf(c_41,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) ),
    inference(demodulation,[status(thm)],[c_40,c_29])).

cnf(c_42,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.70/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.70/1.06  
% 0.70/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.70/1.06  
% 0.70/1.06  ------  iProver source info
% 0.70/1.06  
% 0.70/1.06  git: date: 2020-06-30 10:37:57 +0100
% 0.70/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.70/1.06  git: non_committed_changes: false
% 0.70/1.06  git: last_make_outside_of_git: false
% 0.70/1.06  
% 0.70/1.06  ------ 
% 0.70/1.06  
% 0.70/1.06  ------ Input Options
% 0.70/1.06  
% 0.70/1.06  --out_options                           all
% 0.70/1.06  --tptp_safe_out                         true
% 0.70/1.06  --problem_path                          ""
% 0.70/1.06  --include_path                          ""
% 0.70/1.06  --clausifier                            res/vclausify_rel
% 0.70/1.06  --clausifier_options                    --mode clausify
% 0.70/1.06  --stdin                                 false
% 0.70/1.06  --stats_out                             all
% 0.70/1.06  
% 0.70/1.06  ------ General Options
% 0.70/1.06  
% 0.70/1.06  --fof                                   false
% 0.70/1.06  --time_out_real                         305.
% 0.70/1.06  --time_out_virtual                      -1.
% 0.70/1.06  --symbol_type_check                     false
% 0.70/1.06  --clausify_out                          false
% 0.70/1.06  --sig_cnt_out                           false
% 0.70/1.06  --trig_cnt_out                          false
% 0.70/1.06  --trig_cnt_out_tolerance                1.
% 0.70/1.06  --trig_cnt_out_sk_spl                   false
% 0.70/1.06  --abstr_cl_out                          false
% 0.70/1.06  
% 0.70/1.06  ------ Global Options
% 0.70/1.06  
% 0.70/1.06  --schedule                              default
% 0.70/1.06  --add_important_lit                     false
% 0.70/1.06  --prop_solver_per_cl                    1000
% 0.70/1.06  --min_unsat_core                        false
% 0.70/1.06  --soft_assumptions                      false
% 0.70/1.06  --soft_lemma_size                       3
% 0.70/1.06  --prop_impl_unit_size                   0
% 0.70/1.06  --prop_impl_unit                        []
% 0.70/1.06  --share_sel_clauses                     true
% 0.70/1.06  --reset_solvers                         false
% 0.70/1.06  --bc_imp_inh                            [conj_cone]
% 0.70/1.06  --conj_cone_tolerance                   3.
% 0.70/1.06  --extra_neg_conj                        none
% 0.70/1.06  --large_theory_mode                     true
% 0.70/1.06  --prolific_symb_bound                   200
% 0.70/1.06  --lt_threshold                          2000
% 0.70/1.06  --clause_weak_htbl                      true
% 0.70/1.06  --gc_record_bc_elim                     false
% 0.70/1.06  
% 0.70/1.06  ------ Preprocessing Options
% 0.70/1.06  
% 0.70/1.06  --preprocessing_flag                    true
% 0.70/1.06  --time_out_prep_mult                    0.1
% 0.70/1.06  --splitting_mode                        input
% 0.70/1.06  --splitting_grd                         true
% 0.70/1.06  --splitting_cvd                         false
% 0.70/1.06  --splitting_cvd_svl                     false
% 0.70/1.06  --splitting_nvd                         32
% 0.70/1.06  --sub_typing                            true
% 0.70/1.06  --prep_gs_sim                           true
% 0.70/1.06  --prep_unflatten                        true
% 0.70/1.06  --prep_res_sim                          true
% 0.70/1.06  --prep_upred                            true
% 0.70/1.06  --prep_sem_filter                       exhaustive
% 0.70/1.06  --prep_sem_filter_out                   false
% 0.70/1.06  --pred_elim                             true
% 0.70/1.06  --res_sim_input                         true
% 0.70/1.06  --eq_ax_congr_red                       true
% 0.70/1.06  --pure_diseq_elim                       true
% 0.70/1.06  --brand_transform                       false
% 0.70/1.06  --non_eq_to_eq                          false
% 0.70/1.06  --prep_def_merge                        true
% 0.70/1.06  --prep_def_merge_prop_impl              false
% 0.70/1.06  --prep_def_merge_mbd                    true
% 0.70/1.06  --prep_def_merge_tr_red                 false
% 0.70/1.06  --prep_def_merge_tr_cl                  false
% 0.70/1.06  --smt_preprocessing                     true
% 0.70/1.06  --smt_ac_axioms                         fast
% 0.70/1.06  --preprocessed_out                      false
% 0.70/1.06  --preprocessed_stats                    false
% 0.70/1.06  
% 0.70/1.06  ------ Abstraction refinement Options
% 0.70/1.06  
% 0.70/1.06  --abstr_ref                             []
% 0.70/1.06  --abstr_ref_prep                        false
% 0.70/1.06  --abstr_ref_until_sat                   false
% 0.70/1.06  --abstr_ref_sig_restrict                funpre
% 0.70/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 0.70/1.06  --abstr_ref_under                       []
% 0.70/1.06  
% 0.70/1.06  ------ SAT Options
% 0.70/1.06  
% 0.70/1.06  --sat_mode                              false
% 0.70/1.06  --sat_fm_restart_options                ""
% 0.70/1.06  --sat_gr_def                            false
% 0.70/1.06  --sat_epr_types                         true
% 0.70/1.06  --sat_non_cyclic_types                  false
% 0.70/1.06  --sat_finite_models                     false
% 0.70/1.06  --sat_fm_lemmas                         false
% 0.70/1.06  --sat_fm_prep                           false
% 0.70/1.07  --sat_fm_uc_incr                        true
% 0.70/1.07  --sat_out_model                         small
% 0.70/1.07  --sat_out_clauses                       false
% 0.70/1.07  
% 0.70/1.07  ------ QBF Options
% 0.70/1.07  
% 0.70/1.07  --qbf_mode                              false
% 0.70/1.07  --qbf_elim_univ                         false
% 0.70/1.07  --qbf_dom_inst                          none
% 0.70/1.07  --qbf_dom_pre_inst                      false
% 0.70/1.07  --qbf_sk_in                             false
% 0.70/1.07  --qbf_pred_elim                         true
% 0.70/1.07  --qbf_split                             512
% 0.70/1.07  
% 0.70/1.07  ------ BMC1 Options
% 0.70/1.07  
% 0.70/1.07  --bmc1_incremental                      false
% 0.70/1.07  --bmc1_axioms                           reachable_all
% 0.70/1.07  --bmc1_min_bound                        0
% 0.70/1.07  --bmc1_max_bound                        -1
% 0.70/1.07  --bmc1_max_bound_default                -1
% 0.70/1.07  --bmc1_symbol_reachability              true
% 0.70/1.07  --bmc1_property_lemmas                  false
% 0.70/1.07  --bmc1_k_induction                      false
% 0.70/1.07  --bmc1_non_equiv_states                 false
% 0.70/1.07  --bmc1_deadlock                         false
% 0.70/1.07  --bmc1_ucm                              false
% 0.70/1.07  --bmc1_add_unsat_core                   none
% 0.70/1.07  --bmc1_unsat_core_children              false
% 0.70/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 0.70/1.07  --bmc1_out_stat                         full
% 0.70/1.07  --bmc1_ground_init                      false
% 0.70/1.07  --bmc1_pre_inst_next_state              false
% 0.70/1.07  --bmc1_pre_inst_state                   false
% 0.70/1.07  --bmc1_pre_inst_reach_state             false
% 0.70/1.07  --bmc1_out_unsat_core                   false
% 0.70/1.07  --bmc1_aig_witness_out                  false
% 0.70/1.07  --bmc1_verbose                          false
% 0.70/1.07  --bmc1_dump_clauses_tptp                false
% 0.70/1.07  --bmc1_dump_unsat_core_tptp             false
% 0.70/1.07  --bmc1_dump_file                        -
% 0.70/1.07  --bmc1_ucm_expand_uc_limit              128
% 0.70/1.07  --bmc1_ucm_n_expand_iterations          6
% 0.70/1.07  --bmc1_ucm_extend_mode                  1
% 0.70/1.07  --bmc1_ucm_init_mode                    2
% 0.70/1.07  --bmc1_ucm_cone_mode                    none
% 0.70/1.07  --bmc1_ucm_reduced_relation_type        0
% 0.70/1.07  --bmc1_ucm_relax_model                  4
% 0.70/1.07  --bmc1_ucm_full_tr_after_sat            true
% 0.70/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 0.70/1.07  --bmc1_ucm_layered_model                none
% 0.70/1.07  --bmc1_ucm_max_lemma_size               10
% 0.70/1.07  
% 0.70/1.07  ------ AIG Options
% 0.70/1.07  
% 0.70/1.07  --aig_mode                              false
% 0.70/1.07  
% 0.70/1.07  ------ Instantiation Options
% 0.70/1.07  
% 0.70/1.07  --instantiation_flag                    true
% 0.70/1.07  --inst_sos_flag                         false
% 0.70/1.07  --inst_sos_phase                        true
% 0.70/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.70/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.70/1.07  --inst_lit_sel_side                     num_symb
% 0.70/1.07  --inst_solver_per_active                1400
% 0.70/1.07  --inst_solver_calls_frac                1.
% 0.70/1.07  --inst_passive_queue_type               priority_queues
% 0.70/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.70/1.07  --inst_passive_queues_freq              [25;2]
% 0.70/1.07  --inst_dismatching                      true
% 0.70/1.07  --inst_eager_unprocessed_to_passive     true
% 0.70/1.07  --inst_prop_sim_given                   true
% 0.70/1.07  --inst_prop_sim_new                     false
% 0.70/1.07  --inst_subs_new                         false
% 0.70/1.07  --inst_eq_res_simp                      false
% 0.70/1.07  --inst_subs_given                       false
% 0.70/1.07  --inst_orphan_elimination               true
% 0.70/1.07  --inst_learning_loop_flag               true
% 0.70/1.07  --inst_learning_start                   3000
% 0.70/1.07  --inst_learning_factor                  2
% 0.70/1.07  --inst_start_prop_sim_after_learn       3
% 0.70/1.07  --inst_sel_renew                        solver
% 0.70/1.07  --inst_lit_activity_flag                true
% 0.70/1.07  --inst_restr_to_given                   false
% 0.70/1.07  --inst_activity_threshold               500
% 0.70/1.07  --inst_out_proof                        true
% 0.70/1.07  
% 0.70/1.07  ------ Resolution Options
% 0.70/1.07  
% 0.70/1.07  --resolution_flag                       true
% 0.70/1.07  --res_lit_sel                           adaptive
% 0.70/1.07  --res_lit_sel_side                      none
% 0.70/1.07  --res_ordering                          kbo
% 0.70/1.07  --res_to_prop_solver                    active
% 0.70/1.07  --res_prop_simpl_new                    false
% 0.70/1.07  --res_prop_simpl_given                  true
% 0.70/1.07  --res_passive_queue_type                priority_queues
% 0.70/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.70/1.07  --res_passive_queues_freq               [15;5]
% 0.70/1.07  --res_forward_subs                      full
% 0.70/1.07  --res_backward_subs                     full
% 0.70/1.07  --res_forward_subs_resolution           true
% 0.70/1.07  --res_backward_subs_resolution          true
% 0.70/1.07  --res_orphan_elimination                true
% 0.70/1.07  --res_time_limit                        2.
% 0.70/1.07  --res_out_proof                         true
% 0.70/1.07  
% 0.70/1.07  ------ Superposition Options
% 0.70/1.07  
% 0.70/1.07  --superposition_flag                    true
% 0.70/1.07  --sup_passive_queue_type                priority_queues
% 0.70/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.70/1.07  --sup_passive_queues_freq               [8;1;4]
% 0.70/1.07  --demod_completeness_check              fast
% 0.70/1.07  --demod_use_ground                      true
% 0.70/1.07  --sup_to_prop_solver                    passive
% 0.70/1.07  --sup_prop_simpl_new                    true
% 0.70/1.07  --sup_prop_simpl_given                  true
% 0.70/1.07  --sup_fun_splitting                     false
% 0.70/1.07  --sup_smt_interval                      50000
% 0.70/1.07  
% 0.70/1.07  ------ Superposition Simplification Setup
% 0.70/1.07  
% 0.70/1.07  --sup_indices_passive                   []
% 0.70/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 0.70/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/1.07  --sup_full_bw                           [BwDemod]
% 0.70/1.07  --sup_immed_triv                        [TrivRules]
% 0.70/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.70/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/1.07  --sup_immed_bw_main                     []
% 0.70/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.70/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 0.70/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.70/1.07  
% 0.70/1.07  ------ Combination Options
% 0.70/1.07  
% 0.70/1.07  --comb_res_mult                         3
% 0.70/1.07  --comb_sup_mult                         2
% 0.70/1.07  --comb_inst_mult                        10
% 0.70/1.07  
% 0.70/1.07  ------ Debug Options
% 0.70/1.07  
% 0.70/1.07  --dbg_backtrace                         false
% 0.70/1.07  --dbg_dump_prop_clauses                 false
% 0.70/1.07  --dbg_dump_prop_clauses_file            -
% 0.70/1.07  --dbg_out_stat                          false
% 0.70/1.07  ------ Parsing...
% 0.70/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.70/1.07  
% 0.70/1.07  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 0.70/1.07  
% 0.70/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.70/1.07  
% 0.70/1.07  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.70/1.07  ------ Proving...
% 0.70/1.07  ------ Problem Properties 
% 0.70/1.07  
% 0.70/1.07  
% 0.70/1.07  clauses                                 4
% 0.70/1.07  conjectures                             1
% 0.70/1.07  EPR                                     0
% 0.70/1.07  Horn                                    4
% 0.70/1.07  unary                                   4
% 0.70/1.07  binary                                  0
% 0.70/1.07  lits                                    4
% 0.70/1.07  lits eq                                 4
% 0.70/1.07  fd_pure                                 0
% 0.70/1.07  fd_pseudo                               0
% 0.70/1.07  fd_cond                                 0
% 0.70/1.07  fd_pseudo_cond                          0
% 0.70/1.07  AC symbols                              0
% 0.70/1.07  
% 0.70/1.07  ------ Schedule UEQ
% 0.70/1.07  
% 0.70/1.07  ------ pure equality problem: resolution off 
% 0.70/1.07  
% 0.70/1.07  ------ Option_UEQ Time Limit: Unbounded
% 0.70/1.07  
% 0.70/1.07  
% 0.70/1.07  ------ 
% 0.70/1.07  Current options:
% 0.70/1.07  ------ 
% 0.70/1.07  
% 0.70/1.07  ------ Input Options
% 0.70/1.07  
% 0.70/1.07  --out_options                           all
% 0.70/1.07  --tptp_safe_out                         true
% 0.70/1.07  --problem_path                          ""
% 0.70/1.07  --include_path                          ""
% 0.70/1.07  --clausifier                            res/vclausify_rel
% 0.70/1.07  --clausifier_options                    --mode clausify
% 0.70/1.07  --stdin                                 false
% 0.70/1.07  --stats_out                             all
% 0.70/1.07  
% 0.70/1.07  ------ General Options
% 0.70/1.07  
% 0.70/1.07  --fof                                   false
% 0.70/1.07  --time_out_real                         305.
% 0.70/1.07  --time_out_virtual                      -1.
% 0.70/1.07  --symbol_type_check                     false
% 0.70/1.07  --clausify_out                          false
% 0.70/1.07  --sig_cnt_out                           false
% 0.70/1.07  --trig_cnt_out                          false
% 0.70/1.07  --trig_cnt_out_tolerance                1.
% 0.70/1.07  --trig_cnt_out_sk_spl                   false
% 0.70/1.07  --abstr_cl_out                          false
% 0.70/1.07  
% 0.70/1.07  ------ Global Options
% 0.70/1.07  
% 0.70/1.07  --schedule                              default
% 0.70/1.07  --add_important_lit                     false
% 0.70/1.07  --prop_solver_per_cl                    1000
% 0.70/1.07  --min_unsat_core                        false
% 0.70/1.07  --soft_assumptions                      false
% 0.70/1.07  --soft_lemma_size                       3
% 0.70/1.07  --prop_impl_unit_size                   0
% 0.70/1.07  --prop_impl_unit                        []
% 0.70/1.07  --share_sel_clauses                     true
% 0.70/1.07  --reset_solvers                         false
% 0.70/1.07  --bc_imp_inh                            [conj_cone]
% 0.70/1.07  --conj_cone_tolerance                   3.
% 0.70/1.07  --extra_neg_conj                        none
% 0.70/1.07  --large_theory_mode                     true
% 0.70/1.07  --prolific_symb_bound                   200
% 0.70/1.07  --lt_threshold                          2000
% 0.70/1.07  --clause_weak_htbl                      true
% 0.70/1.07  --gc_record_bc_elim                     false
% 0.70/1.07  
% 0.70/1.07  ------ Preprocessing Options
% 0.70/1.07  
% 0.70/1.07  --preprocessing_flag                    true
% 0.70/1.07  --time_out_prep_mult                    0.1
% 0.70/1.07  --splitting_mode                        input
% 0.70/1.07  --splitting_grd                         true
% 0.70/1.07  --splitting_cvd                         false
% 0.70/1.07  --splitting_cvd_svl                     false
% 0.70/1.07  --splitting_nvd                         32
% 0.70/1.07  --sub_typing                            true
% 0.70/1.07  --prep_gs_sim                           true
% 0.70/1.07  --prep_unflatten                        true
% 0.70/1.07  --prep_res_sim                          true
% 0.70/1.07  --prep_upred                            true
% 0.70/1.07  --prep_sem_filter                       exhaustive
% 0.70/1.07  --prep_sem_filter_out                   false
% 0.70/1.07  --pred_elim                             true
% 0.70/1.07  --res_sim_input                         true
% 0.70/1.07  --eq_ax_congr_red                       true
% 0.70/1.07  --pure_diseq_elim                       true
% 0.70/1.07  --brand_transform                       false
% 0.70/1.07  --non_eq_to_eq                          false
% 0.70/1.07  --prep_def_merge                        true
% 0.70/1.07  --prep_def_merge_prop_impl              false
% 0.70/1.07  --prep_def_merge_mbd                    true
% 0.70/1.07  --prep_def_merge_tr_red                 false
% 0.70/1.07  --prep_def_merge_tr_cl                  false
% 0.70/1.07  --smt_preprocessing                     true
% 0.70/1.07  --smt_ac_axioms                         fast
% 0.70/1.07  --preprocessed_out                      false
% 0.70/1.07  --preprocessed_stats                    false
% 0.70/1.07  
% 0.70/1.07  ------ Abstraction refinement Options
% 0.70/1.07  
% 0.70/1.07  --abstr_ref                             []
% 0.70/1.07  --abstr_ref_prep                        false
% 0.70/1.07  --abstr_ref_until_sat                   false
% 0.70/1.07  --abstr_ref_sig_restrict                funpre
% 0.70/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 0.70/1.07  --abstr_ref_under                       []
% 0.70/1.07  
% 0.70/1.07  ------ SAT Options
% 0.70/1.07  
% 0.70/1.07  --sat_mode                              false
% 0.70/1.07  --sat_fm_restart_options                ""
% 0.70/1.07  --sat_gr_def                            false
% 0.70/1.07  --sat_epr_types                         true
% 0.70/1.07  --sat_non_cyclic_types                  false
% 0.70/1.07  --sat_finite_models                     false
% 0.70/1.07  --sat_fm_lemmas                         false
% 0.70/1.07  --sat_fm_prep                           false
% 0.70/1.07  --sat_fm_uc_incr                        true
% 0.70/1.07  --sat_out_model                         small
% 0.70/1.07  --sat_out_clauses                       false
% 0.70/1.07  
% 0.70/1.07  ------ QBF Options
% 0.70/1.07  
% 0.70/1.07  --qbf_mode                              false
% 0.70/1.07  --qbf_elim_univ                         false
% 0.70/1.07  --qbf_dom_inst                          none
% 0.70/1.07  --qbf_dom_pre_inst                      false
% 0.70/1.07  --qbf_sk_in                             false
% 0.70/1.07  --qbf_pred_elim                         true
% 0.70/1.07  --qbf_split                             512
% 0.70/1.07  
% 0.70/1.07  ------ BMC1 Options
% 0.70/1.07  
% 0.70/1.07  --bmc1_incremental                      false
% 0.70/1.07  --bmc1_axioms                           reachable_all
% 0.70/1.07  --bmc1_min_bound                        0
% 0.70/1.07  --bmc1_max_bound                        -1
% 0.70/1.07  --bmc1_max_bound_default                -1
% 0.70/1.07  --bmc1_symbol_reachability              true
% 0.70/1.07  --bmc1_property_lemmas                  false
% 0.70/1.07  --bmc1_k_induction                      false
% 0.70/1.07  --bmc1_non_equiv_states                 false
% 0.70/1.07  --bmc1_deadlock                         false
% 0.70/1.07  --bmc1_ucm                              false
% 0.70/1.07  --bmc1_add_unsat_core                   none
% 0.70/1.07  --bmc1_unsat_core_children              false
% 0.70/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 0.70/1.07  --bmc1_out_stat                         full
% 0.70/1.07  --bmc1_ground_init                      false
% 0.70/1.07  --bmc1_pre_inst_next_state              false
% 0.70/1.07  --bmc1_pre_inst_state                   false
% 0.70/1.07  --bmc1_pre_inst_reach_state             false
% 0.70/1.07  --bmc1_out_unsat_core                   false
% 0.70/1.07  --bmc1_aig_witness_out                  false
% 0.70/1.07  --bmc1_verbose                          false
% 0.70/1.07  --bmc1_dump_clauses_tptp                false
% 0.70/1.07  --bmc1_dump_unsat_core_tptp             false
% 0.70/1.07  --bmc1_dump_file                        -
% 0.70/1.07  --bmc1_ucm_expand_uc_limit              128
% 0.70/1.07  --bmc1_ucm_n_expand_iterations          6
% 0.70/1.07  --bmc1_ucm_extend_mode                  1
% 0.70/1.07  --bmc1_ucm_init_mode                    2
% 0.70/1.07  --bmc1_ucm_cone_mode                    none
% 0.70/1.07  --bmc1_ucm_reduced_relation_type        0
% 0.70/1.07  --bmc1_ucm_relax_model                  4
% 0.70/1.07  --bmc1_ucm_full_tr_after_sat            true
% 0.70/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 0.70/1.07  --bmc1_ucm_layered_model                none
% 0.70/1.07  --bmc1_ucm_max_lemma_size               10
% 0.70/1.07  
% 0.70/1.07  ------ AIG Options
% 0.70/1.07  
% 0.70/1.07  --aig_mode                              false
% 0.70/1.07  
% 0.70/1.07  ------ Instantiation Options
% 0.70/1.07  
% 0.70/1.07  --instantiation_flag                    false
% 0.70/1.07  --inst_sos_flag                         false
% 0.70/1.07  --inst_sos_phase                        true
% 0.70/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.70/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.70/1.07  --inst_lit_sel_side                     num_symb
% 0.70/1.07  --inst_solver_per_active                1400
% 0.70/1.07  --inst_solver_calls_frac                1.
% 0.70/1.07  --inst_passive_queue_type               priority_queues
% 0.70/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.70/1.07  --inst_passive_queues_freq              [25;2]
% 0.70/1.07  --inst_dismatching                      true
% 0.70/1.07  --inst_eager_unprocessed_to_passive     true
% 0.70/1.07  --inst_prop_sim_given                   true
% 0.70/1.07  --inst_prop_sim_new                     false
% 0.70/1.07  --inst_subs_new                         false
% 0.70/1.07  --inst_eq_res_simp                      false
% 0.70/1.07  --inst_subs_given                       false
% 0.70/1.07  --inst_orphan_elimination               true
% 0.70/1.07  --inst_learning_loop_flag               true
% 0.70/1.07  --inst_learning_start                   3000
% 0.70/1.07  --inst_learning_factor                  2
% 0.70/1.07  --inst_start_prop_sim_after_learn       3
% 0.70/1.07  --inst_sel_renew                        solver
% 0.70/1.07  --inst_lit_activity_flag                true
% 0.70/1.07  --inst_restr_to_given                   false
% 0.70/1.07  --inst_activity_threshold               500
% 0.70/1.07  --inst_out_proof                        true
% 0.70/1.07  
% 0.70/1.07  ------ Resolution Options
% 0.70/1.07  
% 0.70/1.07  --resolution_flag                       false
% 0.70/1.07  --res_lit_sel                           adaptive
% 0.70/1.07  --res_lit_sel_side                      none
% 0.70/1.07  --res_ordering                          kbo
% 0.70/1.07  --res_to_prop_solver                    active
% 0.70/1.07  --res_prop_simpl_new                    false
% 0.70/1.07  --res_prop_simpl_given                  true
% 0.70/1.07  --res_passive_queue_type                priority_queues
% 0.70/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.70/1.07  --res_passive_queues_freq               [15;5]
% 0.70/1.07  --res_forward_subs                      full
% 0.70/1.07  --res_backward_subs                     full
% 0.70/1.07  --res_forward_subs_resolution           true
% 0.70/1.07  --res_backward_subs_resolution          true
% 0.70/1.07  --res_orphan_elimination                true
% 0.70/1.07  --res_time_limit                        2.
% 0.70/1.07  --res_out_proof                         true
% 0.70/1.07  
% 0.70/1.07  ------ Superposition Options
% 0.70/1.07  
% 0.70/1.07  --superposition_flag                    true
% 0.70/1.07  --sup_passive_queue_type                priority_queues
% 0.70/1.07  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.70/1.07  --sup_passive_queues_freq               [8;1;4]
% 0.70/1.07  --demod_completeness_check              fast
% 0.70/1.07  --demod_use_ground                      true
% 0.70/1.07  --sup_to_prop_solver                    active
% 0.70/1.07  --sup_prop_simpl_new                    false
% 0.70/1.07  --sup_prop_simpl_given                  false
% 0.70/1.07  --sup_fun_splitting                     true
% 0.70/1.07  --sup_smt_interval                      10000
% 0.70/1.07  
% 0.70/1.07  ------ Superposition Simplification Setup
% 0.70/1.07  
% 0.70/1.07  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 0.70/1.07  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 0.70/1.07  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.07  --sup_full_triv                         [TrivRules]
% 0.70/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 0.70/1.07  --sup_full_bw                           [BwDemod;BwSubsumption]
% 0.70/1.07  --sup_immed_triv                        [TrivRules]
% 0.70/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.70/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 0.70/1.07  --sup_immed_bw_main                     []
% 0.70/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 0.70/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 0.70/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 0.70/1.07  --sup_input_bw                          [BwDemod;BwSubsumption]
% 0.70/1.07  
% 0.70/1.07  ------ Combination Options
% 0.70/1.07  
% 0.70/1.07  --comb_res_mult                         1
% 0.70/1.07  --comb_sup_mult                         1
% 0.70/1.07  --comb_inst_mult                        1000000
% 0.70/1.07  
% 0.70/1.07  ------ Debug Options
% 0.70/1.07  
% 0.70/1.07  --dbg_backtrace                         false
% 0.70/1.07  --dbg_dump_prop_clauses                 false
% 0.70/1.07  --dbg_dump_prop_clauses_file            -
% 0.70/1.07  --dbg_out_stat                          false
% 0.70/1.07  
% 0.70/1.07  
% 0.70/1.07  
% 0.70/1.07  
% 0.70/1.07  ------ Proving...
% 0.70/1.07  
% 0.70/1.07  
% 0.70/1.07  % SZS status Theorem for theBenchmark.p
% 0.70/1.07  
% 0.70/1.07   Resolution empty clause
% 0.70/1.07  
% 0.70/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 0.70/1.07  
% 0.70/1.07  fof(f6,axiom,(
% 0.70/1.07    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.70/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f19,plain,(
% 0.70/1.07    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.70/1.07    inference(cnf_transformation,[],[f6])).
% 0.70/1.07  
% 0.70/1.07  fof(f3,axiom,(
% 0.70/1.07    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 0.70/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f16,plain,(
% 0.70/1.07    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 0.70/1.07    inference(cnf_transformation,[],[f3])).
% 0.70/1.07  
% 0.70/1.07  fof(f1,axiom,(
% 0.70/1.07    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.70/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f14,plain,(
% 0.70/1.07    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.70/1.07    inference(cnf_transformation,[],[f1])).
% 0.70/1.07  
% 0.70/1.07  fof(f23,plain,(
% 0.70/1.07    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) = k1_enumset1(X0,X1,X2)) )),
% 0.70/1.07    inference(definition_unfolding,[],[f16,f14])).
% 0.70/1.07  
% 0.70/1.07  fof(f27,plain,(
% 0.70/1.07    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))) = k2_tarski(X0,X1)) )),
% 0.70/1.07    inference(definition_unfolding,[],[f19,f23])).
% 0.70/1.07  
% 0.70/1.07  fof(f8,axiom,(
% 0.70/1.07    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.70/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f21,plain,(
% 0.70/1.07    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.70/1.07    inference(cnf_transformation,[],[f8])).
% 0.70/1.07  
% 0.70/1.07  fof(f2,axiom,(
% 0.70/1.07    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.70/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f15,plain,(
% 0.70/1.07    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.70/1.07    inference(cnf_transformation,[],[f2])).
% 0.70/1.07  
% 0.70/1.07  fof(f24,plain,(
% 0.70/1.07    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k2_tarski(X4,X5),k1_tarski(X3))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.70/1.07    inference(definition_unfolding,[],[f15,f14,f23,f23])).
% 0.70/1.07  
% 0.70/1.07  fof(f5,axiom,(
% 0.70/1.07    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.70/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f18,plain,(
% 0.70/1.07    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.70/1.07    inference(cnf_transformation,[],[f5])).
% 0.70/1.07  
% 0.70/1.07  fof(f26,plain,(
% 0.70/1.07    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.70/1.07    inference(definition_unfolding,[],[f18,f14,f23])).
% 0.70/1.07  
% 0.70/1.07  fof(f29,plain,(
% 0.70/1.07    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0)))))) )),
% 0.70/1.07    inference(definition_unfolding,[],[f21,f24,f26])).
% 0.70/1.07  
% 0.70/1.07  fof(f7,axiom,(
% 0.70/1.07    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.70/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f20,plain,(
% 0.70/1.07    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.70/1.07    inference(cnf_transformation,[],[f7])).
% 0.70/1.07  
% 0.70/1.07  fof(f4,axiom,(
% 0.70/1.07    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 0.70/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f17,plain,(
% 0.70/1.07    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.70/1.07    inference(cnf_transformation,[],[f4])).
% 0.70/1.07  
% 0.70/1.07  fof(f25,plain,(
% 0.70/1.07    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.70/1.07    inference(definition_unfolding,[],[f17,f14,f23])).
% 0.70/1.07  
% 0.70/1.07  fof(f28,plain,(
% 0.70/1.07    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))),k4_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0)))))) )),
% 0.70/1.07    inference(definition_unfolding,[],[f20,f25,f26])).
% 0.70/1.07  
% 0.70/1.07  fof(f9,conjecture,(
% 0.70/1.07    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)),
% 0.70/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f10,negated_conjecture,(
% 0.70/1.07    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)),
% 0.70/1.07    inference(negated_conjecture,[],[f9])).
% 0.70/1.07  
% 0.70/1.07  fof(f11,plain,(
% 0.70/1.07    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k3_enumset1(X0,X0,X0,X1,X2)),
% 0.70/1.07    inference(ennf_transformation,[],[f10])).
% 0.70/1.07  
% 0.70/1.07  fof(f12,plain,(
% 0.70/1.07    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k3_enumset1(X0,X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 0.70/1.07    introduced(choice_axiom,[])).
% 0.70/1.07  
% 0.70/1.07  fof(f13,plain,(
% 0.70/1.07    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 0.70/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 0.70/1.07  
% 0.70/1.07  fof(f22,plain,(
% 0.70/1.07    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 0.70/1.07    inference(cnf_transformation,[],[f13])).
% 0.70/1.07  
% 0.70/1.07  fof(f30,plain,(
% 0.70/1.07    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))),k4_xboole_0(k2_tarski(sK1,sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0)))))),
% 0.70/1.07    inference(definition_unfolding,[],[f22,f23,f26])).
% 0.70/1.07  
% 0.70/1.07  cnf(c_0,plain,
% 0.70/1.07      ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))) = k2_tarski(X0,X1) ),
% 0.70/1.07      inference(cnf_transformation,[],[f27]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_16,plain,
% 0.70/1.07      ( k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X0_37,X1_37),k1_tarski(X0_37))) = k2_tarski(X0_37,X1_37) ),
% 0.70/1.07      inference(subtyping,[status(esa)],[c_0]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_2,plain,
% 0.70/1.07      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))))) ),
% 0.70/1.07      inference(cnf_transformation,[],[f29]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_14,plain,
% 0.70/1.07      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X0_37,X1_37),k1_tarski(X0_37))),k4_xboole_0(k5_xboole_0(k1_tarski(X2_37),k4_xboole_0(k2_tarski(X3_37,X4_37),k1_tarski(X2_37))),k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X0_37,X1_37),k1_tarski(X0_37))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k1_tarski(X0_37))),k4_xboole_0(k2_tarski(X3_37,X4_37),k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k1_tarski(X0_37))))) ),
% 0.70/1.07      inference(subtyping,[status(esa)],[c_2]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_31,plain,
% 0.70/1.07      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k1_tarski(X0_37))),k4_xboole_0(k2_tarski(X3_37,X4_37),k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k1_tarski(X0_37))))) = k5_xboole_0(k2_tarski(X0_37,X1_37),k4_xboole_0(k5_xboole_0(k1_tarski(X2_37),k4_xboole_0(k2_tarski(X3_37,X4_37),k1_tarski(X2_37))),k2_tarski(X0_37,X1_37))) ),
% 0.70/1.07      inference(light_normalisation,[status(thm)],[c_14,c_16]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_36,plain,
% 0.70/1.07      ( k5_xboole_0(k2_tarski(X0_37,X0_37),k4_xboole_0(k5_xboole_0(k1_tarski(X1_37),k4_xboole_0(k2_tarski(X2_37,X3_37),k1_tarski(X1_37))),k2_tarski(X0_37,X0_37))) = k5_xboole_0(k2_tarski(X0_37,X1_37),k4_xboole_0(k2_tarski(X2_37,X3_37),k2_tarski(X0_37,X1_37))) ),
% 0.70/1.07      inference(superposition,[status(thm)],[c_16,c_31]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_39,plain,
% 0.70/1.07      ( k5_xboole_0(k2_tarski(X0_37,X0_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k2_tarski(X0_37,X0_37))) = k5_xboole_0(k2_tarski(X0_37,X1_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k2_tarski(X0_37,X1_37))) ),
% 0.70/1.07      inference(superposition,[status(thm)],[c_16,c_36]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_1,plain,
% 0.70/1.07      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))),k4_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))) ),
% 0.70/1.07      inference(cnf_transformation,[],[f28]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_15,plain,
% 0.70/1.07      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X0_37,X1_37),k1_tarski(X0_37))),k4_xboole_0(k2_tarski(X2_37,X3_37),k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X0_37,X1_37),k1_tarski(X0_37))))) = k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k5_xboole_0(k1_tarski(X1_37),k4_xboole_0(k2_tarski(X2_37,X3_37),k1_tarski(X1_37))),k1_tarski(X0_37))) ),
% 0.70/1.07      inference(subtyping,[status(esa)],[c_1]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_30,plain,
% 0.70/1.07      ( k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k5_xboole_0(k1_tarski(X1_37),k4_xboole_0(k2_tarski(X2_37,X3_37),k1_tarski(X1_37))),k1_tarski(X0_37))) = k5_xboole_0(k2_tarski(X0_37,X1_37),k4_xboole_0(k2_tarski(X2_37,X3_37),k2_tarski(X0_37,X1_37))) ),
% 0.70/1.07      inference(light_normalisation,[status(thm)],[c_15,c_16]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_33,plain,
% 0.70/1.07      ( k5_xboole_0(k2_tarski(X0_37,X1_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k2_tarski(X0_37,X1_37))) = k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k1_tarski(X0_37))) ),
% 0.70/1.07      inference(superposition,[status(thm)],[c_16,c_30]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_40,plain,
% 0.70/1.07      ( k5_xboole_0(k2_tarski(X0_37,X0_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k2_tarski(X0_37,X0_37))) = k5_xboole_0(k1_tarski(X0_37),k4_xboole_0(k2_tarski(X1_37,X2_37),k1_tarski(X0_37))) ),
% 0.70/1.07      inference(light_normalisation,[status(thm)],[c_39,c_33]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_3,negated_conjecture,
% 0.70/1.07      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))),k4_xboole_0(k2_tarski(sK1,sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))))) ),
% 0.70/1.07      inference(cnf_transformation,[],[f30]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_13,negated_conjecture,
% 0.70/1.07      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))),k4_xboole_0(k2_tarski(sK1,sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))))) ),
% 0.70/1.07      inference(subtyping,[status(esa)],[c_3]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_29,plain,
% 0.70/1.07      ( k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) ),
% 0.70/1.07      inference(demodulation,[status(thm)],[c_13,c_16]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_41,plain,
% 0.70/1.07      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) ),
% 0.70/1.07      inference(demodulation,[status(thm)],[c_40,c_29]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_42,plain,
% 0.70/1.07      ( $false ),
% 0.70/1.07      inference(equality_resolution_simp,[status(thm)],[c_41]) ).
% 0.70/1.07  
% 0.70/1.07  
% 0.70/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 0.70/1.07  
% 0.70/1.07  ------                               Statistics
% 0.70/1.07  
% 0.70/1.07  ------ General
% 0.70/1.07  
% 0.70/1.07  abstr_ref_over_cycles:                  0
% 0.70/1.07  abstr_ref_under_cycles:                 0
% 0.70/1.07  gc_basic_clause_elim:                   0
% 0.70/1.07  forced_gc_time:                         0
% 0.70/1.07  parsing_time:                           0.009
% 0.70/1.07  unif_index_cands_time:                  0.
% 0.70/1.07  unif_index_add_time:                    0.
% 0.70/1.07  orderings_time:                         0.
% 0.70/1.07  out_proof_time:                         0.007
% 0.70/1.07  total_time:                             0.043
% 0.70/1.07  num_of_symbols:                         38
% 0.70/1.07  num_of_terms:                           246
% 0.70/1.07  
% 0.70/1.07  ------ Preprocessing
% 0.70/1.07  
% 0.70/1.07  num_of_splits:                          0
% 0.70/1.07  num_of_split_atoms:                     0
% 0.70/1.07  num_of_reused_defs:                     0
% 0.70/1.07  num_eq_ax_congr_red:                    3
% 0.70/1.07  num_of_sem_filtered_clauses:            0
% 0.70/1.07  num_of_subtypes:                        3
% 0.70/1.07  monotx_restored_types:                  0
% 0.70/1.07  sat_num_of_epr_types:                   0
% 0.70/1.07  sat_num_of_non_cyclic_types:            0
% 0.70/1.07  sat_guarded_non_collapsed_types:        0
% 0.70/1.07  num_pure_diseq_elim:                    0
% 0.70/1.07  simp_replaced_by:                       0
% 0.70/1.07  res_preprocessed:                       13
% 0.70/1.07  prep_upred:                             0
% 0.70/1.07  prep_unflattend:                        0
% 0.70/1.07  smt_new_axioms:                         0
% 0.70/1.07  pred_elim_cands:                        0
% 0.70/1.07  pred_elim:                              0
% 0.70/1.07  pred_elim_cl:                           0
% 0.70/1.07  pred_elim_cycles:                       0
% 0.70/1.07  merged_defs:                            0
% 0.70/1.07  merged_defs_ncl:                        0
% 0.70/1.07  bin_hyper_res:                          0
% 0.70/1.07  prep_cycles:                            2
% 0.70/1.07  pred_elim_time:                         0.
% 0.70/1.07  splitting_time:                         0.
% 0.70/1.07  sem_filter_time:                        0.
% 0.70/1.07  monotx_time:                            0.
% 0.70/1.07  subtype_inf_time:                       0.
% 0.70/1.07  
% 0.70/1.07  ------ Problem properties
% 0.70/1.07  
% 0.70/1.07  clauses:                                4
% 0.70/1.07  conjectures:                            1
% 0.70/1.07  epr:                                    0
% 0.70/1.07  horn:                                   4
% 0.70/1.07  ground:                                 1
% 0.70/1.07  unary:                                  4
% 0.70/1.07  binary:                                 0
% 0.70/1.07  lits:                                   4
% 0.70/1.07  lits_eq:                                4
% 0.70/1.07  fd_pure:                                0
% 0.70/1.07  fd_pseudo:                              0
% 0.70/1.07  fd_cond:                                0
% 0.70/1.07  fd_pseudo_cond:                         0
% 0.70/1.07  ac_symbols:                             0
% 0.70/1.07  
% 0.70/1.07  ------ Propositional Solver
% 0.70/1.07  
% 0.70/1.07  prop_solver_calls:                      13
% 0.70/1.07  prop_fast_solver_calls:                 38
% 0.70/1.07  smt_solver_calls:                       0
% 0.70/1.07  smt_fast_solver_calls:                  0
% 0.70/1.07  prop_num_of_clauses:                    33
% 0.70/1.07  prop_preprocess_simplified:             155
% 0.70/1.07  prop_fo_subsumed:                       0
% 0.70/1.07  prop_solver_time:                       0.
% 0.70/1.07  smt_solver_time:                        0.
% 0.70/1.07  smt_fast_solver_time:                   0.
% 0.70/1.07  prop_fast_solver_time:                  0.
% 0.70/1.07  prop_unsat_core_time:                   0.
% 0.70/1.07  
% 0.70/1.07  ------ QBF
% 0.70/1.07  
% 0.70/1.07  qbf_q_res:                              0
% 0.70/1.07  qbf_num_tautologies:                    0
% 0.70/1.07  qbf_prep_cycles:                        0
% 0.70/1.07  
% 0.70/1.07  ------ BMC1
% 0.70/1.07  
% 0.70/1.07  bmc1_current_bound:                     -1
% 0.70/1.07  bmc1_last_solved_bound:                 -1
% 0.70/1.07  bmc1_unsat_core_size:                   -1
% 0.70/1.07  bmc1_unsat_core_parents_size:           -1
% 0.70/1.07  bmc1_merge_next_fun:                    0
% 0.70/1.07  bmc1_unsat_core_clauses_time:           0.
% 0.70/1.07  
% 0.70/1.07  ------ Instantiation
% 0.70/1.07  
% 0.70/1.07  inst_num_of_clauses:                    0
% 0.70/1.07  inst_num_in_passive:                    0
% 0.70/1.07  inst_num_in_active:                     0
% 0.70/1.07  inst_num_in_unprocessed:                0
% 0.70/1.07  inst_num_of_loops:                      0
% 0.70/1.07  inst_num_of_learning_restarts:          0
% 0.70/1.07  inst_num_moves_active_passive:          0
% 0.70/1.07  inst_lit_activity:                      0
% 0.70/1.07  inst_lit_activity_moves:                0
% 0.70/1.07  inst_num_tautologies:                   0
% 0.70/1.07  inst_num_prop_implied:                  0
% 0.70/1.07  inst_num_existing_simplified:           0
% 0.70/1.07  inst_num_eq_res_simplified:             0
% 0.70/1.07  inst_num_child_elim:                    0
% 0.70/1.07  inst_num_of_dismatching_blockings:      0
% 0.70/1.07  inst_num_of_non_proper_insts:           0
% 0.70/1.07  inst_num_of_duplicates:                 0
% 0.70/1.07  inst_inst_num_from_inst_to_res:         0
% 0.70/1.07  inst_dismatching_checking_time:         0.
% 0.70/1.07  
% 0.70/1.07  ------ Resolution
% 0.70/1.07  
% 0.70/1.07  res_num_of_clauses:                     0
% 0.70/1.07  res_num_in_passive:                     0
% 0.70/1.07  res_num_in_active:                      0
% 0.70/1.07  res_num_of_loops:                       15
% 0.70/1.07  res_forward_subset_subsumed:            0
% 0.70/1.07  res_backward_subset_subsumed:           0
% 0.70/1.07  res_forward_subsumed:                   0
% 0.70/1.07  res_backward_subsumed:                  0
% 0.70/1.07  res_forward_subsumption_resolution:     0
% 0.70/1.07  res_backward_subsumption_resolution:    0
% 0.70/1.07  res_clause_to_clause_subsumption:       14
% 0.70/1.07  res_orphan_elimination:                 0
% 0.70/1.07  res_tautology_del:                      0
% 0.70/1.07  res_num_eq_res_simplified:              0
% 0.70/1.07  res_num_sel_changes:                    0
% 0.70/1.07  res_moves_from_active_to_pass:          0
% 0.70/1.07  
% 0.70/1.07  ------ Superposition
% 0.70/1.07  
% 0.70/1.07  sup_time_total:                         0.
% 0.70/1.07  sup_time_generating:                    0.
% 0.70/1.07  sup_time_sim_full:                      0.
% 0.70/1.07  sup_time_sim_immed:                     0.
% 0.70/1.07  
% 0.70/1.07  sup_num_of_clauses:                     7
% 0.70/1.07  sup_num_in_active:                      6
% 0.70/1.07  sup_num_in_passive:                     1
% 0.70/1.07  sup_num_of_loops:                       7
% 0.70/1.07  sup_fw_superposition:                   4
% 0.70/1.07  sup_bw_superposition:                   0
% 0.70/1.07  sup_immediate_simplified:               1
% 0.70/1.07  sup_given_eliminated:                   0
% 0.70/1.07  comparisons_done:                       0
% 0.70/1.07  comparisons_avoided:                    0
% 0.70/1.07  
% 0.70/1.07  ------ Simplifications
% 0.70/1.07  
% 0.70/1.07  
% 0.70/1.07  sim_fw_subset_subsumed:                 0
% 0.70/1.07  sim_bw_subset_subsumed:                 0
% 0.70/1.07  sim_fw_subsumed:                        0
% 0.70/1.07  sim_bw_subsumed:                        0
% 0.70/1.07  sim_fw_subsumption_res:                 0
% 0.70/1.07  sim_bw_subsumption_res:                 0
% 0.70/1.07  sim_tautology_del:                      0
% 0.70/1.07  sim_eq_tautology_del:                   0
% 0.70/1.07  sim_eq_res_simp:                        0
% 0.70/1.07  sim_fw_demodulated:                     1
% 0.70/1.07  sim_bw_demodulated:                     1
% 0.70/1.07  sim_light_normalised:                   3
% 0.70/1.07  sim_joinable_taut:                      0
% 0.70/1.07  sim_joinable_simp:                      0
% 0.70/1.07  sim_ac_normalised:                      0
% 0.70/1.07  sim_smt_subsumption:                    0
% 0.70/1.07  
%------------------------------------------------------------------------------
