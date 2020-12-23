%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:56 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 144 expanded)
%              Number of clauses        :   21 (  51 expanded)
%              Number of leaves         :   10 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 ( 145 expanded)
%              Number of equality atoms :   47 ( 144 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f20,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f21,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f38,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f38,f24,f34])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f28,f34])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f27,f34])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_10,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_4115,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_4155,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_4115])).

cnf(c_13,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_51,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_13,c_10,c_0])).

cnf(c_7708,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_4155,c_51])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_4237,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_4])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_4124,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_4])).

cnf(c_4156,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4124,c_4115])).

cnf(c_4496,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4156])).

cnf(c_4759,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4237,c_4496])).

cnf(c_4792,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4759,c_4124])).

cnf(c_4751,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_4496])).

cnf(c_4804,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_4751,c_4496])).

cnf(c_7709,plain,
    ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_7708,c_4792,c_4804])).

cnf(c_8481,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7709,c_0])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:38:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.79/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/0.99  
% 3.79/0.99  ------  iProver source info
% 3.79/0.99  
% 3.79/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.79/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/0.99  git: non_committed_changes: false
% 3.79/0.99  git: last_make_outside_of_git: false
% 3.79/0.99  
% 3.79/0.99  ------ 
% 3.79/0.99  ------ Parsing...
% 3.79/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  ------ Proving...
% 3.79/0.99  ------ Problem Properties 
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  clauses                                 14
% 3.79/0.99  conjectures                             1
% 3.79/0.99  EPR                                     0
% 3.79/0.99  Horn                                    14
% 3.79/0.99  unary                                   13
% 3.79/0.99  binary                                  0
% 3.79/0.99  lits                                    17
% 3.79/0.99  lits eq                                 14
% 3.79/0.99  fd_pure                                 0
% 3.79/0.99  fd_pseudo                               0
% 3.79/0.99  fd_cond                                 0
% 3.79/0.99  fd_pseudo_cond                          1
% 3.79/0.99  AC symbols                              1
% 3.79/0.99  
% 3.79/0.99  ------ Input Options Time Limit: Unbounded
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing...
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.79/0.99  Current options:
% 3.79/0.99  ------ 
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  % SZS status Theorem for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99   Resolution empty clause
% 3.79/0.99  
% 3.79/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  fof(f8,axiom,(
% 3.79/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f30,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f8])).
% 3.79/0.99  
% 3.79/0.99  fof(f13,axiom,(
% 3.79/0.99    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f35,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f13])).
% 3.79/0.99  
% 3.79/0.99  fof(f1,axiom,(
% 3.79/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f23,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f1])).
% 3.79/0.99  
% 3.79/0.99  fof(f16,conjecture,(
% 3.79/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f17,negated_conjecture,(
% 3.79/0.99    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.79/0.99    inference(negated_conjecture,[],[f16])).
% 3.79/0.99  
% 3.79/0.99  fof(f20,plain,(
% 3.79/0.99    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.79/0.99    inference(ennf_transformation,[],[f17])).
% 3.79/0.99  
% 3.79/0.99  fof(f21,plain,(
% 3.79/0.99    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f22,plain,(
% 3.79/0.99    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).
% 3.79/0.99  
% 3.79/0.99  fof(f38,plain,(
% 3.79/0.99    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.79/0.99    inference(cnf_transformation,[],[f22])).
% 3.79/0.99  
% 3.79/0.99  fof(f2,axiom,(
% 3.79/0.99    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f24,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f2])).
% 3.79/0.99  
% 3.79/0.99  fof(f12,axiom,(
% 3.79/0.99    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f34,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f12])).
% 3.79/0.99  
% 3.79/0.99  fof(f45,plain,(
% 3.79/0.99    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 3.79/0.99    inference(definition_unfolding,[],[f38,f24,f34])).
% 3.79/0.99  
% 3.79/0.99  fof(f11,axiom,(
% 3.79/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f33,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f11])).
% 3.79/0.99  
% 3.79/0.99  fof(f43,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.79/0.99    inference(definition_unfolding,[],[f33,f34])).
% 3.79/0.99  
% 3.79/0.99  fof(f6,axiom,(
% 3.79/0.99    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f28,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.79/0.99    inference(cnf_transformation,[],[f6])).
% 3.79/0.99  
% 3.79/0.99  fof(f41,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 3.79/0.99    inference(definition_unfolding,[],[f28,f34])).
% 3.79/0.99  
% 3.79/0.99  fof(f5,axiom,(
% 3.79/0.99    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f27,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 3.79/0.99    inference(cnf_transformation,[],[f5])).
% 3.79/0.99  
% 3.79/0.99  fof(f40,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 3.79/0.99    inference(definition_unfolding,[],[f27,f34])).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6,plain,
% 3.79/0.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.79/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_10,plain,
% 3.79/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.79/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_0,plain,
% 3.79/0.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f23]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4115,plain,
% 3.79/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4155,plain,
% 3.79/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_6,c_4115]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_13,negated_conjecture,
% 3.79/0.99      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 3.79/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_51,negated_conjecture,
% 3.79/0.99      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 3.79/0.99      inference(theory_normalisation,[status(thm)],[c_13,c_10,c_0]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_7708,plain,
% 3.79/0.99      ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) != k2_xboole_0(sK0,sK1) ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_4155,c_51]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9,plain,
% 3.79/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.79/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4,plain,
% 3.79/0.99      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.79/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4237,plain,
% 3.79/0.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_9,c_4]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3,plain,
% 3.79/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
% 3.79/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4124,plain,
% 3.79/0.99      ( k2_xboole_0(X0,X0) = X0 ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_3,c_4]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4156,plain,
% 3.79/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_4124,c_4115]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4496,plain,
% 3.79/0.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_0,c_4156]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4759,plain,
% 3.79/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X0) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_4237,c_4496]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4792,plain,
% 3.79/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 3.79/0.99      inference(light_normalisation,[status(thm)],[c_4759,c_4124]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4751,plain,
% 3.79/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_6,c_4496]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4804,plain,
% 3.79/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_4751,c_4496]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_7709,plain,
% 3.79/0.99      ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_7708,c_4792,c_4804]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_8481,plain,
% 3.79/0.99      ( $false ),
% 3.79/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_7709,c_0]) ).
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  ------                               Statistics
% 3.79/0.99  
% 3.79/0.99  ------ Selected
% 3.79/0.99  
% 3.79/0.99  total_time:                             0.179
% 3.79/0.99  
%------------------------------------------------------------------------------
