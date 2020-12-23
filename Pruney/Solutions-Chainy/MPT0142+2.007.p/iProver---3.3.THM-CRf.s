%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:32 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 108 expanded)
%              Number of clauses        :    7 (  11 expanded)
%              Number of leaves         :    9 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   35 ( 109 expanded)
%              Number of equality atoms :   34 ( 108 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   12 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f15,f17,f17,f17,f17])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) != k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(ennf_transformation,[],[f11])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) != k5_enumset1(X0,X1,X2,X3,X4,X5,X6)
   => k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f13])).

fof(f24,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f21,f17,f26])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f19,f17])).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f20,f17,f25])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k1_tarski(X3))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f18,f17,f26,f26])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))),k1_tarski(X4))),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))))),k1_tarski(X0))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f23,f17,f27])).

fof(f32,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) ),
    inference(definition_unfolding,[],[f24,f17,f26,f28,f29])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_15,plain,
    ( k5_xboole_0(k5_xboole_0(X0_39,k4_xboole_0(X1_39,X0_39)),k4_xboole_0(X2_39,k5_xboole_0(X0_39,k4_xboole_0(X1_39,X0_39)))) = k5_xboole_0(X0_39,k4_xboole_0(k5_xboole_0(X1_39,k4_xboole_0(X2_39,X1_39)),X0_39)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_106,plain,
    ( k5_xboole_0(k5_xboole_0(X0_39,k4_xboole_0(k5_xboole_0(X1_39,k4_xboole_0(X2_39,X1_39)),X0_39)),k4_xboole_0(X3_39,k5_xboole_0(X0_39,k4_xboole_0(k5_xboole_0(X1_39,k4_xboole_0(X2_39,X1_39)),X0_39)))) = k5_xboole_0(k5_xboole_0(X0_39,k4_xboole_0(X1_39,X0_39)),k4_xboole_0(k5_xboole_0(X2_39,k4_xboole_0(X3_39,X2_39)),k5_xboole_0(X0_39,k4_xboole_0(X1_39,X0_39)))) ),
    inference(superposition,[status(thm)],[c_15,c_15])).

cnf(c_3,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_12,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_103,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k1_tarski(sK0))) ),
    inference(superposition,[status(thm)],[c_15,c_12])).

cnf(c_1730,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_106,c_103])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.59/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.00  
% 2.59/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.59/1.00  
% 2.59/1.00  ------  iProver source info
% 2.59/1.00  
% 2.59/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.59/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.59/1.00  git: non_committed_changes: false
% 2.59/1.00  git: last_make_outside_of_git: false
% 2.59/1.00  
% 2.59/1.00  ------ 
% 2.59/1.00  ------ Parsing...
% 2.59/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.59/1.00  
% 2.59/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.59/1.00  
% 2.59/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.59/1.00  
% 2.59/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.59/1.00  ------ Proving...
% 2.59/1.00  ------ Problem Properties 
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  clauses                                 4
% 2.59/1.00  conjectures                             1
% 2.59/1.00  EPR                                     0
% 2.59/1.00  Horn                                    4
% 2.59/1.00  unary                                   4
% 2.59/1.00  binary                                  0
% 2.59/1.00  lits                                    4
% 2.59/1.00  lits eq                                 4
% 2.59/1.00  fd_pure                                 0
% 2.59/1.00  fd_pseudo                               0
% 2.59/1.00  fd_cond                                 0
% 2.59/1.00  fd_pseudo_cond                          0
% 2.59/1.00  AC symbols                              0
% 2.59/1.00  
% 2.59/1.00  ------ Input Options Time Limit: Unbounded
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  ------ 
% 2.59/1.00  Current options:
% 2.59/1.00  ------ 
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  ------ Proving...
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  % SZS status Theorem for theBenchmark.p
% 2.59/1.00  
% 2.59/1.00   Resolution empty clause
% 2.59/1.00  
% 2.59/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.59/1.00  
% 2.59/1.00  fof(f1,axiom,(
% 2.59/1.00    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 2.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f15,plain,(
% 2.59/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f1])).
% 2.59/1.00  
% 2.59/1.00  fof(f3,axiom,(
% 2.59/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f17,plain,(
% 2.59/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.59/1.00    inference(cnf_transformation,[],[f3])).
% 2.59/1.00  
% 2.59/1.00  fof(f30,plain,(
% 2.59/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 2.59/1.00    inference(definition_unfolding,[],[f15,f17,f17,f17,f17])).
% 2.59/1.00  
% 2.59/1.00  fof(f10,conjecture,(
% 2.59/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f11,negated_conjecture,(
% 2.59/1.00    ~! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.59/1.00    inference(negated_conjecture,[],[f10])).
% 2.59/1.00  
% 2.59/1.00  fof(f12,plain,(
% 2.59/1.00    ? [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) != k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.59/1.00    inference(ennf_transformation,[],[f11])).
% 2.59/1.00  
% 2.59/1.00  fof(f13,plain,(
% 2.59/1.00    ? [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) != k5_enumset1(X0,X1,X2,X3,X4,X5,X6) => k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 2.59/1.00    introduced(choice_axiom,[])).
% 2.59/1.00  
% 2.59/1.00  fof(f14,plain,(
% 2.59/1.00    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 2.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f13])).
% 2.59/1.00  
% 2.59/1.00  fof(f24,plain,(
% 2.59/1.00    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 2.59/1.00    inference(cnf_transformation,[],[f14])).
% 2.59/1.00  
% 2.59/1.00  fof(f7,axiom,(
% 2.59/1.00    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f21,plain,(
% 2.59/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f7])).
% 2.59/1.00  
% 2.59/1.00  fof(f28,plain,(
% 2.59/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.59/1.00    inference(definition_unfolding,[],[f21,f17,f26])).
% 2.59/1.00  
% 2.59/1.00  fof(f9,axiom,(
% 2.59/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f23,plain,(
% 2.59/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f9])).
% 2.59/1.00  
% 2.59/1.00  fof(f4,axiom,(
% 2.59/1.00    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f18,plain,(
% 2.59/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f4])).
% 2.59/1.00  
% 2.59/1.00  fof(f6,axiom,(
% 2.59/1.00    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 2.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f20,plain,(
% 2.59/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f6])).
% 2.59/1.00  
% 2.59/1.00  fof(f5,axiom,(
% 2.59/1.00    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 2.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f19,plain,(
% 2.59/1.00    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f5])).
% 2.59/1.00  
% 2.59/1.00  fof(f25,plain,(
% 2.59/1.00    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1)) )),
% 2.59/1.00    inference(definition_unfolding,[],[f19,f17])).
% 2.59/1.00  
% 2.59/1.00  fof(f26,plain,(
% 2.59/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) = k1_enumset1(X0,X1,X2)) )),
% 2.59/1.00    inference(definition_unfolding,[],[f20,f17,f25])).
% 2.59/1.00  
% 2.59/1.00  fof(f27,plain,(
% 2.59/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k1_tarski(X3))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.59/1.00    inference(definition_unfolding,[],[f18,f17,f26,f26])).
% 2.59/1.00  
% 2.59/1.00  fof(f29,plain,(
% 2.59/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))),k1_tarski(X4))),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))))),k1_tarski(X0))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.59/1.00    inference(definition_unfolding,[],[f23,f17,f27])).
% 2.59/1.00  
% 2.59/1.00  fof(f32,plain,(
% 2.59/1.00    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0)))),
% 2.59/1.00    inference(definition_unfolding,[],[f24,f17,f26,f28,f29])).
% 2.59/1.00  
% 2.59/1.00  cnf(c_0,plain,
% 2.59/1.00      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
% 2.59/1.00      inference(cnf_transformation,[],[f30]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_15,plain,
% 2.59/1.00      ( k5_xboole_0(k5_xboole_0(X0_39,k4_xboole_0(X1_39,X0_39)),k4_xboole_0(X2_39,k5_xboole_0(X0_39,k4_xboole_0(X1_39,X0_39)))) = k5_xboole_0(X0_39,k4_xboole_0(k5_xboole_0(X1_39,k4_xboole_0(X2_39,X1_39)),X0_39)) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_106,plain,
% 2.59/1.00      ( k5_xboole_0(k5_xboole_0(X0_39,k4_xboole_0(k5_xboole_0(X1_39,k4_xboole_0(X2_39,X1_39)),X0_39)),k4_xboole_0(X3_39,k5_xboole_0(X0_39,k4_xboole_0(k5_xboole_0(X1_39,k4_xboole_0(X2_39,X1_39)),X0_39)))) = k5_xboole_0(k5_xboole_0(X0_39,k4_xboole_0(X1_39,X0_39)),k4_xboole_0(k5_xboole_0(X2_39,k4_xboole_0(X3_39,X2_39)),k5_xboole_0(X0_39,k4_xboole_0(X1_39,X0_39)))) ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_15,c_15]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3,negated_conjecture,
% 2.59/1.00      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) ),
% 2.59/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_12,negated_conjecture,
% 2.59/1.00      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_103,plain,
% 2.59/1.00      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k1_tarski(sK0))) ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_15,c_12]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1730,plain,
% 2.59/1.00      ( $false ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_106,c_103]) ).
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.59/1.00  
% 2.59/1.00  ------                               Statistics
% 2.59/1.00  
% 2.59/1.00  ------ Selected
% 2.59/1.00  
% 2.59/1.00  total_time:                             0.136
% 2.59/1.00  
%------------------------------------------------------------------------------
