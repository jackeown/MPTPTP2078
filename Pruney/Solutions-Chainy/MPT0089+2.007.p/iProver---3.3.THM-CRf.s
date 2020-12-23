%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:37 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   37 (  52 expanded)
%              Number of clauses        :   18 (  23 expanded)
%              Number of leaves         :    8 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :   38 (  53 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f12,f16])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f8])).

fof(f10,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
   => ~ r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f18,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_3,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_85,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_0,c_2])).

cnf(c_466,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_85])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_468,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_466,c_1])).

cnf(c_463,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_3,c_1])).

cnf(c_1463,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_468,c_463])).

cnf(c_4,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_80,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_465,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_80])).

cnf(c_4373,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k4_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1463,c_465])).

cnf(c_462,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_4421,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4373,c_462])).

cnf(c_5,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_79,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7624,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4421,c_79])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:18:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.83/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.02  
% 3.83/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.83/1.02  
% 3.83/1.02  ------  iProver source info
% 3.83/1.02  
% 3.83/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.83/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.83/1.02  git: non_committed_changes: false
% 3.83/1.02  git: last_make_outside_of_git: false
% 3.83/1.02  
% 3.83/1.02  ------ 
% 3.83/1.02  ------ Parsing...
% 3.83/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.83/1.02  
% 3.83/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.83/1.02  
% 3.83/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.83/1.02  
% 3.83/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.83/1.02  ------ Proving...
% 3.83/1.02  ------ Problem Properties 
% 3.83/1.02  
% 3.83/1.02  
% 3.83/1.02  clauses                                 6
% 3.83/1.02  conjectures                             1
% 3.83/1.02  EPR                                     0
% 3.83/1.02  Horn                                    6
% 3.83/1.02  unary                                   6
% 3.83/1.02  binary                                  0
% 3.83/1.02  lits                                    6
% 3.83/1.02  lits eq                                 4
% 3.83/1.02  fd_pure                                 0
% 3.83/1.02  fd_pseudo                               0
% 3.83/1.02  fd_cond                                 0
% 3.83/1.02  fd_pseudo_cond                          0
% 3.83/1.02  AC symbols                              0
% 3.83/1.02  
% 3.83/1.02  ------ Input Options Time Limit: Unbounded
% 3.83/1.02  
% 3.83/1.02  
% 3.83/1.02  ------ 
% 3.83/1.02  Current options:
% 3.83/1.02  ------ 
% 3.83/1.02  
% 3.83/1.02  
% 3.83/1.02  
% 3.83/1.02  
% 3.83/1.02  ------ Proving...
% 3.83/1.02  
% 3.83/1.02  
% 3.83/1.02  % SZS status Theorem for theBenchmark.p
% 3.83/1.02  
% 3.83/1.02   Resolution empty clause
% 3.83/1.02  
% 3.83/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.83/1.02  
% 3.83/1.02  fof(f4,axiom,(
% 3.83/1.02    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.83/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.02  
% 3.83/1.02  fof(f15,plain,(
% 3.83/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.83/1.02    inference(cnf_transformation,[],[f4])).
% 3.83/1.02  
% 3.83/1.02  fof(f1,axiom,(
% 3.83/1.02    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.83/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.02  
% 3.83/1.02  fof(f12,plain,(
% 3.83/1.02    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.83/1.02    inference(cnf_transformation,[],[f1])).
% 3.83/1.02  
% 3.83/1.02  fof(f5,axiom,(
% 3.83/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.83/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.02  
% 3.83/1.02  fof(f16,plain,(
% 3.83/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.83/1.02    inference(cnf_transformation,[],[f5])).
% 3.83/1.02  
% 3.83/1.02  fof(f19,plain,(
% 3.83/1.02    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.83/1.02    inference(definition_unfolding,[],[f12,f16])).
% 3.83/1.02  
% 3.83/1.02  fof(f3,axiom,(
% 3.83/1.02    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.83/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.02  
% 3.83/1.02  fof(f14,plain,(
% 3.83/1.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.83/1.02    inference(cnf_transformation,[],[f3])).
% 3.83/1.02  
% 3.83/1.02  fof(f2,axiom,(
% 3.83/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.83/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.02  
% 3.83/1.02  fof(f13,plain,(
% 3.83/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.83/1.02    inference(cnf_transformation,[],[f2])).
% 3.83/1.02  
% 3.83/1.02  fof(f6,axiom,(
% 3.83/1.02    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.83/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.02  
% 3.83/1.02  fof(f17,plain,(
% 3.83/1.02    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.83/1.02    inference(cnf_transformation,[],[f6])).
% 3.83/1.02  
% 3.83/1.02  fof(f7,conjecture,(
% 3.83/1.02    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.83/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.02  
% 3.83/1.02  fof(f8,negated_conjecture,(
% 3.83/1.02    ~! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.83/1.02    inference(negated_conjecture,[],[f7])).
% 3.83/1.02  
% 3.83/1.02  fof(f9,plain,(
% 3.83/1.02    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.83/1.02    inference(ennf_transformation,[],[f8])).
% 3.83/1.02  
% 3.83/1.02  fof(f10,plain,(
% 3.83/1.02    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) => ~r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 3.83/1.02    introduced(choice_axiom,[])).
% 3.83/1.02  
% 3.83/1.02  fof(f11,plain,(
% 3.83/1.02    ~r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 3.83/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 3.83/1.02  
% 3.83/1.02  fof(f18,plain,(
% 3.83/1.02    ~r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 3.83/1.02    inference(cnf_transformation,[],[f11])).
% 3.83/1.02  
% 3.83/1.02  cnf(c_3,plain,
% 3.83/1.02      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.83/1.02      inference(cnf_transformation,[],[f15]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_0,plain,
% 3.83/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.83/1.02      inference(cnf_transformation,[],[f19]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_2,plain,
% 3.83/1.02      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.83/1.02      inference(cnf_transformation,[],[f14]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_85,plain,
% 3.83/1.02      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.83/1.02      inference(light_normalisation,[status(thm)],[c_0,c_2]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_466,plain,
% 3.83/1.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 3.83/1.02      inference(superposition,[status(thm)],[c_3,c_85]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_1,plain,
% 3.83/1.02      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.83/1.02      inference(cnf_transformation,[],[f13]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_468,plain,
% 3.83/1.02      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 3.83/1.02      inference(demodulation,[status(thm)],[c_466,c_1]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_463,plain,
% 3.83/1.02      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.83/1.02      inference(superposition,[status(thm)],[c_3,c_1]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_1463,plain,
% 3.83/1.02      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 3.83/1.02      inference(superposition,[status(thm)],[c_468,c_463]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_4,plain,
% 3.83/1.02      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 3.83/1.02      inference(cnf_transformation,[],[f17]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_80,plain,
% 3.83/1.02      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 3.83/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_465,plain,
% 3.83/1.02      ( r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = iProver_top ),
% 3.83/1.02      inference(superposition,[status(thm)],[c_3,c_80]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_4373,plain,
% 3.83/1.02      ( r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k4_xboole_0(X1,X2)) = iProver_top ),
% 3.83/1.02      inference(superposition,[status(thm)],[c_1463,c_465]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_462,plain,
% 3.83/1.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
% 3.83/1.02      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_4421,plain,
% 3.83/1.02      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = iProver_top ),
% 3.83/1.02      inference(light_normalisation,[status(thm)],[c_4373,c_462]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_5,negated_conjecture,
% 3.83/1.02      ( ~ r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
% 3.83/1.02      inference(cnf_transformation,[],[f18]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_79,plain,
% 3.83/1.02      ( r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != iProver_top ),
% 3.83/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.83/1.02  
% 3.83/1.02  cnf(c_7624,plain,
% 3.83/1.02      ( $false ),
% 3.83/1.02      inference(superposition,[status(thm)],[c_4421,c_79]) ).
% 3.83/1.02  
% 3.83/1.02  
% 3.83/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.83/1.02  
% 3.83/1.02  ------                               Statistics
% 3.83/1.02  
% 3.83/1.02  ------ Selected
% 3.83/1.02  
% 3.83/1.02  total_time:                             0.244
% 3.83/1.02  
%------------------------------------------------------------------------------
