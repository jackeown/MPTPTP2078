%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:51 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 128 expanded)
%              Number of clauses        :   32 (  50 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :   83 ( 194 expanded)
%              Number of equality atoms :   40 (  97 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f25,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f30,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f25,f18])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f22,f18,f18])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f21,f18])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f24,f18])).

fof(f26,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_1,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_2758,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2825,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2758])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_2757,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3031,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2825,c_2757])).

cnf(c_11936,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3031,c_0])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2752,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2805,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_2752])).

cnf(c_3030,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK0 ),
    inference(superposition,[status(thm)],[c_2805,c_2757])).

cnf(c_4,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2756,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2882,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_2756])).

cnf(c_3223,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2882])).

cnf(c_3654,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3223])).

cnf(c_5091,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3030,c_3654])).

cnf(c_5236,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_5091,c_2757])).

cnf(c_12362,plain,
    ( k3_xboole_0(sK1,sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_11936,c_5236])).

cnf(c_6,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2754,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2883,plain,
    ( r1_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_2754])).

cnf(c_2938,plain,
    ( r1_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2883])).

cnf(c_3070,plain,
    ( r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3030,c_2938])).

cnf(c_7,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_102,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | k3_xboole_0(X0,X1) != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_103,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | k3_xboole_0(sK1,X0) != sK0 ),
    inference(unflattening,[status(thm)],[c_102])).

cnf(c_104,plain,
    ( k3_xboole_0(sK1,X0) != sK0
    | r1_xboole_0(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_103])).

cnf(c_106,plain,
    ( k3_xboole_0(sK1,sK0) != sK0
    | r1_xboole_0(sK0,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12362,c_3070,c_106])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:16:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.62/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/0.99  
% 3.62/0.99  ------  iProver source info
% 3.62/0.99  
% 3.62/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.62/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/0.99  git: non_committed_changes: false
% 3.62/0.99  git: last_make_outside_of_git: false
% 3.62/0.99  
% 3.62/0.99  ------ 
% 3.62/0.99  ------ Parsing...
% 3.62/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.99  ------ Proving...
% 3.62/0.99  ------ Problem Properties 
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  clauses                                 9
% 3.62/0.99  conjectures                             2
% 3.62/0.99  EPR                                     2
% 3.62/0.99  Horn                                    9
% 3.62/0.99  unary                                   6
% 3.62/0.99  binary                                  2
% 3.62/0.99  lits                                    13
% 3.62/0.99  lits eq                                 3
% 3.62/0.99  fd_pure                                 0
% 3.62/0.99  fd_pseudo                               0
% 3.62/0.99  fd_cond                                 0
% 3.62/0.99  fd_pseudo_cond                          0
% 3.62/0.99  AC symbols                              0
% 3.62/0.99  
% 3.62/0.99  ------ Input Options Time Limit: Unbounded
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing...
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.62/0.99  Current options:
% 3.62/0.99  ------ 
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ Proving...
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.62/0.99  
% 3.62/0.99  ------ Proving...
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.99  
% 3.62/0.99  ------ Proving...
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.62/0.99  
% 3.62/0.99  ------ Proving...
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.99  
% 3.62/0.99  ------ Proving...
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.62/0.99  
% 3.62/0.99  ------ Proving...
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.99  
% 3.62/0.99  ------ Proving...
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.62/0.99  
% 3.62/0.99  ------ Proving...
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  % SZS status Theorem for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  fof(f1,axiom,(
% 3.62/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f17,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f1])).
% 3.62/0.99  
% 3.62/0.99  fof(f3,axiom,(
% 3.62/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f19,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f3])).
% 3.62/0.99  
% 3.62/0.99  fof(f4,axiom,(
% 3.62/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f11,plain,(
% 3.62/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.62/0.99    inference(ennf_transformation,[],[f4])).
% 3.62/0.99  
% 3.62/0.99  fof(f20,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f11])).
% 3.62/0.99  
% 3.62/0.99  fof(f9,conjecture,(
% 3.62/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f10,negated_conjecture,(
% 3.62/0.99    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.62/0.99    inference(negated_conjecture,[],[f9])).
% 3.62/0.99  
% 3.62/0.99  fof(f14,plain,(
% 3.62/0.99    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.62/0.99    inference(ennf_transformation,[],[f10])).
% 3.62/0.99  
% 3.62/0.99  fof(f15,plain,(
% 3.62/0.99    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f16,plain,(
% 3.62/0.99    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 3.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 3.62/0.99  
% 3.62/0.99  fof(f25,plain,(
% 3.62/0.99    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 3.62/0.99    inference(cnf_transformation,[],[f16])).
% 3.62/0.99  
% 3.62/0.99  fof(f2,axiom,(
% 3.62/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f18,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f2])).
% 3.62/0.99  
% 3.62/0.99  fof(f30,plain,(
% 3.62/0.99    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 3.62/0.99    inference(definition_unfolding,[],[f25,f18])).
% 3.62/0.99  
% 3.62/0.99  fof(f6,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f22,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f6])).
% 3.62/0.99  
% 3.62/0.99  fof(f28,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 3.62/0.99    inference(definition_unfolding,[],[f22,f18,f18])).
% 3.62/0.99  
% 3.62/0.99  fof(f5,axiom,(
% 3.62/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f21,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f5])).
% 3.62/0.99  
% 3.62/0.99  fof(f27,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.62/0.99    inference(definition_unfolding,[],[f21,f18])).
% 3.62/0.99  
% 3.62/0.99  fof(f8,axiom,(
% 3.62/0.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f24,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f8])).
% 3.62/0.99  
% 3.62/0.99  fof(f29,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 3.62/0.99    inference(definition_unfolding,[],[f24,f18])).
% 3.62/0.99  
% 3.62/0.99  fof(f26,plain,(
% 3.62/0.99    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 3.62/0.99    inference(cnf_transformation,[],[f16])).
% 3.62/0.99  
% 3.62/0.99  cnf(c_0,plain,
% 3.62/0.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f17]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1,plain,
% 3.62/0.99      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f19]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2758,plain,
% 3.62/0.99      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2825,plain,
% 3.62/0.99      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_0,c_2758]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2,plain,
% 3.62/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.62/0.99      inference(cnf_transformation,[],[f20]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2757,plain,
% 3.62/0.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3031,plain,
% 3.62/0.99      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_2825,c_2757]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_11936,plain,
% 3.62/0.99      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_3031,c_0]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_8,negated_conjecture,
% 3.62/0.99      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 3.62/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2752,plain,
% 3.62/0.99      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2805,plain,
% 3.62/0.99      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_0,c_2752]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3030,plain,
% 3.62/0.99      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK0 ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_2805,c_2757]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4,plain,
% 3.62/0.99      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.62/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3,plain,
% 3.62/0.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f27]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2756,plain,
% 3.62/0.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2882,plain,
% 3.62/0.99      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_4,c_2756]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3223,plain,
% 3.62/0.99      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X0,X1)) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_0,c_2882]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3654,plain,
% 3.62/0.99      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X1,X0)) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_0,c_3223]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5091,plain,
% 3.62/0.99      ( r1_tarski(sK0,k3_xboole_0(sK1,sK0)) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_3030,c_3654]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5236,plain,
% 3.62/0.99      ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK0)) = sK0 ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_5091,c_2757]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12362,plain,
% 3.62/0.99      ( k3_xboole_0(sK1,sK0) = sK0 ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_11936,c_5236]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6,plain,
% 3.62/0.99      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2754,plain,
% 3.62/0.99      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2883,plain,
% 3.62/0.99      ( r1_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_4,c_2754]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2938,plain,
% 3.62/0.99      ( r1_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),X2) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_0,c_2883]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3070,plain,
% 3.62/0.99      ( r1_xboole_0(sK0,sK2) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_3030,c_2938]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_7,negated_conjecture,
% 3.62/0.99      ( ~ r1_xboole_0(sK0,sK2) | ~ r1_tarski(sK0,sK1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f26]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_102,plain,
% 3.62/0.99      ( ~ r1_xboole_0(sK0,sK2) | k3_xboole_0(X0,X1) != sK0 | sK1 != X0 ),
% 3.62/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_7]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_103,plain,
% 3.62/0.99      ( ~ r1_xboole_0(sK0,sK2) | k3_xboole_0(sK1,X0) != sK0 ),
% 3.62/0.99      inference(unflattening,[status(thm)],[c_102]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_104,plain,
% 3.62/0.99      ( k3_xboole_0(sK1,X0) != sK0
% 3.62/0.99      | r1_xboole_0(sK0,sK2) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_103]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_106,plain,
% 3.62/0.99      ( k3_xboole_0(sK1,sK0) != sK0
% 3.62/0.99      | r1_xboole_0(sK0,sK2) != iProver_top ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_104]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(contradiction,plain,
% 3.62/0.99      ( $false ),
% 3.62/0.99      inference(minisat,[status(thm)],[c_12362,c_3070,c_106]) ).
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  ------                               Statistics
% 3.62/0.99  
% 3.62/0.99  ------ Selected
% 3.62/0.99  
% 3.62/0.99  total_time:                             0.311
% 3.62/0.99  
%------------------------------------------------------------------------------
