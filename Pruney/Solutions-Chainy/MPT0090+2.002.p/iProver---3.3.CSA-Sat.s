%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:38 EST 2020

% Result     : CounterSatisfiable 3.46s
% Output     : Saturation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   52 (  80 expanded)
%              Number of clauses        :   23 (  32 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 159 expanded)
%              Number of equality atoms :   45 (  70 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f14])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f23,f26])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f17,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ( k4_xboole_0(X0,X1) != X0
          | ~ r1_xboole_0(X0,X1) )
        & ( k4_xboole_0(X0,X1) = X0
          | r1_xboole_0(X0,X1) ) )
   => ( ( k4_xboole_0(sK0,sK1) != sK0
        | ~ r1_xboole_0(sK0,sK1) )
      & ( k4_xboole_0(sK0,sK1) = sK0
        | r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ( k4_xboole_0(sK0,sK1) != sK0
      | ~ r1_xboole_0(sK0,sK1) )
    & ( k4_xboole_0(sK0,sK1) = sK0
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f31,plain,
    ( k4_xboole_0(sK0,sK1) = sK0
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,
    ( k4_xboole_0(sK0,sK1) != sK0
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_104,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_152,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_7,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_603,plain,
    ( ~ iProver_ARSWP_24
    | k4_xboole_0(X0,k4_xboole_0(X0,arAF0_k2_xboole_0_0)) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_2])).

cnf(c_717,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,arAF0_k2_xboole_0_0)) = X0
    | iProver_ARSWP_24 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_6,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_723,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_724,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_989,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_723,c_724])).

cnf(c_1104,plain,
    ( r1_xboole_0(k4_xboole_0(X0,arAF0_k2_xboole_0_0),X0) = iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_717,c_989])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_720,plain,
    ( k4_xboole_0(sK0,sK1) = sK0
    | r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_990,plain,
    ( k4_xboole_0(sK0,sK1) = sK0
    | r1_xboole_0(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_720,c_724])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_722,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1265,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k4_xboole_0(X1,X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_722,c_724])).

cnf(c_913,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X0,arAF0_k2_xboole_0_0)) = iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_717,c_723])).

cnf(c_9,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) != sK0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_721,plain,
    ( k4_xboole_0(sK0,sK1) != sK0
    | r1_xboole_0(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:31:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.46/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.02  
% 3.46/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.46/1.02  
% 3.46/1.02  ------  iProver source info
% 3.46/1.02  
% 3.46/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.46/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.46/1.02  git: non_committed_changes: false
% 3.46/1.02  git: last_make_outside_of_git: false
% 3.46/1.02  
% 3.46/1.02  ------ 
% 3.46/1.02  ------ Parsing...
% 3.46/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.46/1.02  
% 3.46/1.02  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 2 0s  sf_e 
% 3.46/1.02  
% 3.46/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.46/1.02  
% 3.46/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/1.02  ------ Proving...
% 3.46/1.02  ------ Problem Properties 
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  clauses                                 8
% 3.46/1.02  conjectures                             2
% 3.46/1.02  EPR                                     1
% 3.46/1.02  Horn                                    7
% 3.46/1.02  unary                                   4
% 3.46/1.02  binary                                  4
% 3.46/1.02  lits                                    12
% 3.46/1.02  lits eq                                 5
% 3.46/1.02  fd_pure                                 0
% 3.46/1.02  fd_pseudo                               0
% 3.46/1.02  fd_cond                                 0
% 3.46/1.02  fd_pseudo_cond                          0
% 3.46/1.02  AC symbols                              0
% 3.46/1.02  
% 3.46/1.02  ------ Input Options Time Limit: Unbounded
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  ------ Preprocessing...
% 3.46/1.02  
% 3.46/1.02  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.46/1.02  Current options:
% 3.46/1.02  ------ 
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  ------ Proving...
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/1.02  
% 3.46/1.02  ------ Proving...
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/1.02  
% 3.46/1.02  ------ Proving...
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/1.02  
% 3.46/1.02  ------ Proving...
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/1.02  
% 3.46/1.02  ------ Proving...
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.46/1.02  
% 3.46/1.02  ------ Proving...
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  % SZS status CounterSatisfiable for theBenchmark.p
% 3.46/1.02  
% 3.46/1.02  % SZS output start Saturation for theBenchmark.p
% 3.46/1.02  
% 3.46/1.02  fof(f9,axiom,(
% 3.46/1.02    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f29,plain,(
% 3.46/1.02    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.46/1.02    inference(cnf_transformation,[],[f9])).
% 3.46/1.02  
% 3.46/1.02  fof(f7,axiom,(
% 3.46/1.02    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f14,plain,(
% 3.46/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 3.46/1.02    inference(ennf_transformation,[],[f7])).
% 3.46/1.02  
% 3.46/1.02  fof(f15,plain,(
% 3.46/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.46/1.02    inference(flattening,[],[f14])).
% 3.46/1.02  
% 3.46/1.02  fof(f27,plain,(
% 3.46/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.46/1.02    inference(cnf_transformation,[],[f15])).
% 3.46/1.02  
% 3.46/1.02  fof(f4,axiom,(
% 3.46/1.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f24,plain,(
% 3.46/1.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.46/1.02    inference(cnf_transformation,[],[f4])).
% 3.46/1.02  
% 3.46/1.02  fof(f3,axiom,(
% 3.46/1.02    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f23,plain,(
% 3.46/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 3.46/1.02    inference(cnf_transformation,[],[f3])).
% 3.46/1.02  
% 3.46/1.02  fof(f6,axiom,(
% 3.46/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f26,plain,(
% 3.46/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.46/1.02    inference(cnf_transformation,[],[f6])).
% 3.46/1.02  
% 3.46/1.02  fof(f33,plain,(
% 3.46/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 3.46/1.02    inference(definition_unfolding,[],[f23,f26])).
% 3.46/1.02  
% 3.46/1.02  fof(f8,axiom,(
% 3.46/1.02    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f28,plain,(
% 3.46/1.02    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.46/1.02    inference(cnf_transformation,[],[f8])).
% 3.46/1.02  
% 3.46/1.02  fof(f2,axiom,(
% 3.46/1.02    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f13,plain,(
% 3.46/1.02    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.46/1.02    inference(ennf_transformation,[],[f2])).
% 3.46/1.02  
% 3.46/1.02  fof(f22,plain,(
% 3.46/1.02    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.46/1.02    inference(cnf_transformation,[],[f13])).
% 3.46/1.02  
% 3.46/1.02  fof(f11,conjecture,(
% 3.46/1.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f12,negated_conjecture,(
% 3.46/1.02    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.46/1.02    inference(negated_conjecture,[],[f11])).
% 3.46/1.02  
% 3.46/1.02  fof(f17,plain,(
% 3.46/1.02    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 3.46/1.02    inference(ennf_transformation,[],[f12])).
% 3.46/1.02  
% 3.46/1.02  fof(f18,plain,(
% 3.46/1.02    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 3.46/1.02    inference(nnf_transformation,[],[f17])).
% 3.46/1.02  
% 3.46/1.02  fof(f19,plain,(
% 3.46/1.02    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((k4_xboole_0(sK0,sK1) != sK0 | ~r1_xboole_0(sK0,sK1)) & (k4_xboole_0(sK0,sK1) = sK0 | r1_xboole_0(sK0,sK1)))),
% 3.46/1.02    introduced(choice_axiom,[])).
% 3.46/1.02  
% 3.46/1.02  fof(f20,plain,(
% 3.46/1.02    (k4_xboole_0(sK0,sK1) != sK0 | ~r1_xboole_0(sK0,sK1)) & (k4_xboole_0(sK0,sK1) = sK0 | r1_xboole_0(sK0,sK1))),
% 3.46/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 3.46/1.02  
% 3.46/1.02  fof(f31,plain,(
% 3.46/1.02    k4_xboole_0(sK0,sK1) = sK0 | r1_xboole_0(sK0,sK1)),
% 3.46/1.02    inference(cnf_transformation,[],[f20])).
% 3.46/1.02  
% 3.46/1.02  fof(f10,axiom,(
% 3.46/1.02    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 3.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.02  
% 3.46/1.02  fof(f16,plain,(
% 3.46/1.02    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 3.46/1.02    inference(ennf_transformation,[],[f10])).
% 3.46/1.02  
% 3.46/1.02  fof(f30,plain,(
% 3.46/1.02    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 3.46/1.02    inference(cnf_transformation,[],[f16])).
% 3.46/1.02  
% 3.46/1.02  fof(f32,plain,(
% 3.46/1.02    k4_xboole_0(sK0,sK1) != sK0 | ~r1_xboole_0(sK0,sK1)),
% 3.46/1.02    inference(cnf_transformation,[],[f20])).
% 3.46/1.02  
% 3.46/1.02  cnf(c_104,plain,
% 3.46/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.46/1.02      theory(equality) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_152,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_7,plain,
% 3.46/1.02      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.46/1.02      inference(cnf_transformation,[],[f29]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_5,plain,
% 3.46/1.02      ( r1_tarski(X0,X1)
% 3.46/1.02      | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 3.46/1.02      | ~ r1_xboole_0(X0,X2) ),
% 3.46/1.02      inference(cnf_transformation,[],[f27]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_3,plain,
% 3.46/1.02      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.46/1.02      inference(cnf_transformation,[],[f24]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_2,plain,
% 3.46/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
% 3.46/1.02      inference(cnf_transformation,[],[f33]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_603,plain,
% 3.46/1.02      ( ~ iProver_ARSWP_24
% 3.46/1.02      | k4_xboole_0(X0,k4_xboole_0(X0,arAF0_k2_xboole_0_0)) = X0 ),
% 3.46/1.02      inference(arg_filter_abstr,[status(unp)],[c_2]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_717,plain,
% 3.46/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,arAF0_k2_xboole_0_0)) = X0
% 3.46/1.02      | iProver_ARSWP_24 != iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_6,plain,
% 3.46/1.02      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 3.46/1.02      inference(cnf_transformation,[],[f28]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_723,plain,
% 3.46/1.02      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1,plain,
% 3.46/1.02      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.46/1.02      inference(cnf_transformation,[],[f22]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_724,plain,
% 3.46/1.02      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_989,plain,
% 3.46/1.02      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_723,c_724]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1104,plain,
% 3.46/1.02      ( r1_xboole_0(k4_xboole_0(X0,arAF0_k2_xboole_0_0),X0) = iProver_top
% 3.46/1.02      | iProver_ARSWP_24 != iProver_top ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_717,c_989]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_10,negated_conjecture,
% 3.46/1.02      ( r1_xboole_0(sK0,sK1) | k4_xboole_0(sK0,sK1) = sK0 ),
% 3.46/1.02      inference(cnf_transformation,[],[f31]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_720,plain,
% 3.46/1.02      ( k4_xboole_0(sK0,sK1) = sK0 | r1_xboole_0(sK0,sK1) = iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_990,plain,
% 3.46/1.02      ( k4_xboole_0(sK0,sK1) = sK0 | r1_xboole_0(sK1,sK0) = iProver_top ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_720,c_724]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_8,plain,
% 3.46/1.02      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.46/1.02      inference(cnf_transformation,[],[f30]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_722,plain,
% 3.46/1.02      ( r1_xboole_0(X0,X1) != iProver_top
% 3.46/1.02      | r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_1265,plain,
% 3.46/1.02      ( r1_xboole_0(X0,X1) != iProver_top
% 3.46/1.02      | r1_xboole_0(k4_xboole_0(X1,X2),X0) = iProver_top ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_722,c_724]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_913,plain,
% 3.46/1.02      ( r1_xboole_0(X0,k4_xboole_0(X0,arAF0_k2_xboole_0_0)) = iProver_top
% 3.46/1.02      | iProver_ARSWP_24 != iProver_top ),
% 3.46/1.02      inference(superposition,[status(thm)],[c_717,c_723]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_9,negated_conjecture,
% 3.46/1.02      ( ~ r1_xboole_0(sK0,sK1) | k4_xboole_0(sK0,sK1) != sK0 ),
% 3.46/1.02      inference(cnf_transformation,[],[f32]) ).
% 3.46/1.02  
% 3.46/1.02  cnf(c_721,plain,
% 3.46/1.02      ( k4_xboole_0(sK0,sK1) != sK0 | r1_xboole_0(sK0,sK1) != iProver_top ),
% 3.46/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.46/1.02  
% 3.46/1.02  
% 3.46/1.02  % SZS output end Saturation for theBenchmark.p
% 3.46/1.02  
% 3.46/1.02  ------                               Statistics
% 3.46/1.02  
% 3.46/1.02  ------ Selected
% 3.46/1.02  
% 3.46/1.02  total_time:                             0.082
% 3.46/1.02  
%------------------------------------------------------------------------------
