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
% DateTime   : Thu Dec  3 11:25:00 EST 2020

% Result     : Theorem 27.95s
% Output     : CNFRefutation 27.95s
% Verified   : 
% Statistics : Number of formulae       :   51 (  67 expanded)
%              Number of clauses        :   26 (  30 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 (  98 expanded)
%              Number of equality atoms :   66 (  88 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f18,f21,f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f13,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f14,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f24,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f24,f17,f17,f21])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f17,f21])).

cnf(c_47,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_390,plain,
    ( X0 != X1
    | X0 = k2_xboole_0(sK0,sK1)
    | k2_xboole_0(sK0,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_10529,plain,
    ( X0 != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | X0 = k2_xboole_0(sK0,sK1)
    | k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_114096,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) = k2_xboole_0(sK0,sK1)
    | k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_10529])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_27006,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_102,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_101,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_300,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_102,c_101])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_6,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_406,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_10815,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_300,c_406])).

cnf(c_2938,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_142,plain,
    ( X0 != X1
    | k2_xboole_0(sK0,sK1) != X1
    | k2_xboole_0(sK0,sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_1049,plain,
    ( X0 != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | k2_xboole_0(sK0,sK1) = X0
    | k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_2937,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_5,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_388,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k2_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_205,plain,
    ( X0 != k2_xboole_0(sK0,sK1)
    | k2_xboole_0(sK0,sK1) = X0
    | k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_387,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1)
    | k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_205])).

cnf(c_46,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_141,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_114096,c_27006,c_10815,c_2938,c_2937,c_388,c_387,c_141])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:13:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 27.95/4.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.95/4.03  
% 27.95/4.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.95/4.03  
% 27.95/4.03  ------  iProver source info
% 27.95/4.03  
% 27.95/4.03  git: date: 2020-06-30 10:37:57 +0100
% 27.95/4.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.95/4.03  git: non_committed_changes: false
% 27.95/4.03  git: last_make_outside_of_git: false
% 27.95/4.03  
% 27.95/4.03  ------ 
% 27.95/4.03  ------ Parsing...
% 27.95/4.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.95/4.03  
% 27.95/4.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.95/4.03  
% 27.95/4.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.95/4.03  
% 27.95/4.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.95/4.03  ------ Proving...
% 27.95/4.03  ------ Problem Properties 
% 27.95/4.03  
% 27.95/4.03  
% 27.95/4.03  clauses                                 7
% 27.95/4.03  conjectures                             1
% 27.95/4.03  EPR                                     0
% 27.95/4.03  Horn                                    7
% 27.95/4.03  unary                                   6
% 27.95/4.03  binary                                  1
% 27.95/4.03  lits                                    8
% 27.95/4.03  lits eq                                 6
% 27.95/4.03  fd_pure                                 0
% 27.95/4.03  fd_pseudo                               0
% 27.95/4.03  fd_cond                                 0
% 27.95/4.03  fd_pseudo_cond                          0
% 27.95/4.03  AC symbols                              0
% 27.95/4.03  
% 27.95/4.03  ------ Input Options Time Limit: Unbounded
% 27.95/4.03  
% 27.95/4.03  
% 27.95/4.03  ------ 
% 27.95/4.03  Current options:
% 27.95/4.03  ------ 
% 27.95/4.03  
% 27.95/4.03  
% 27.95/4.03  
% 27.95/4.03  
% 27.95/4.03  ------ Proving...
% 27.95/4.03  
% 27.95/4.03  
% 27.95/4.03  % SZS status Theorem for theBenchmark.p
% 27.95/4.03  
% 27.95/4.03  % SZS output start CNFRefutation for theBenchmark.p
% 27.95/4.03  
% 27.95/4.03  fof(f4,axiom,(
% 27.95/4.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 27.95/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.95/4.03  
% 27.95/4.03  fof(f19,plain,(
% 27.95/4.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 27.95/4.03    inference(cnf_transformation,[],[f4])).
% 27.95/4.03  
% 27.95/4.03  fof(f3,axiom,(
% 27.95/4.03    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 27.95/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.95/4.03  
% 27.95/4.03  fof(f18,plain,(
% 27.95/4.03    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 27.95/4.03    inference(cnf_transformation,[],[f3])).
% 27.95/4.03  
% 27.95/4.03  fof(f6,axiom,(
% 27.95/4.03    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 27.95/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.95/4.03  
% 27.95/4.03  fof(f21,plain,(
% 27.95/4.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 27.95/4.03    inference(cnf_transformation,[],[f6])).
% 27.95/4.03  
% 27.95/4.03  fof(f2,axiom,(
% 27.95/4.03    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 27.95/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.95/4.03  
% 27.95/4.03  fof(f17,plain,(
% 27.95/4.03    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 27.95/4.03    inference(cnf_transformation,[],[f2])).
% 27.95/4.03  
% 27.95/4.03  fof(f25,plain,(
% 27.95/4.03    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 27.95/4.03    inference(definition_unfolding,[],[f18,f21,f17])).
% 27.95/4.03  
% 27.95/4.03  fof(f7,axiom,(
% 27.95/4.03    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 27.95/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.95/4.03  
% 27.95/4.03  fof(f11,plain,(
% 27.95/4.03    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 27.95/4.03    inference(unused_predicate_definition_removal,[],[f7])).
% 27.95/4.03  
% 27.95/4.03  fof(f12,plain,(
% 27.95/4.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 27.95/4.03    inference(ennf_transformation,[],[f11])).
% 27.95/4.03  
% 27.95/4.03  fof(f22,plain,(
% 27.95/4.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 27.95/4.03    inference(cnf_transformation,[],[f12])).
% 27.95/4.03  
% 27.95/4.03  fof(f1,axiom,(
% 27.95/4.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 27.95/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.95/4.03  
% 27.95/4.03  fof(f16,plain,(
% 27.95/4.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 27.95/4.03    inference(cnf_transformation,[],[f1])).
% 27.95/4.03  
% 27.95/4.03  fof(f9,conjecture,(
% 27.95/4.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 27.95/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.95/4.03  
% 27.95/4.03  fof(f10,negated_conjecture,(
% 27.95/4.03    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 27.95/4.03    inference(negated_conjecture,[],[f9])).
% 27.95/4.03  
% 27.95/4.03  fof(f13,plain,(
% 27.95/4.03    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 27.95/4.03    inference(ennf_transformation,[],[f10])).
% 27.95/4.03  
% 27.95/4.03  fof(f14,plain,(
% 27.95/4.03    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 27.95/4.03    introduced(choice_axiom,[])).
% 27.95/4.03  
% 27.95/4.03  fof(f15,plain,(
% 27.95/4.03    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 27.95/4.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 27.95/4.03  
% 27.95/4.03  fof(f24,plain,(
% 27.95/4.03    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 27.95/4.03    inference(cnf_transformation,[],[f15])).
% 27.95/4.03  
% 27.95/4.03  fof(f27,plain,(
% 27.95/4.03    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 27.95/4.03    inference(definition_unfolding,[],[f24,f17,f17,f21])).
% 27.95/4.03  
% 27.95/4.03  fof(f8,axiom,(
% 27.95/4.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 27.95/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.95/4.03  
% 27.95/4.03  fof(f23,plain,(
% 27.95/4.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 27.95/4.03    inference(cnf_transformation,[],[f8])).
% 27.95/4.03  
% 27.95/4.03  fof(f26,plain,(
% 27.95/4.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 27.95/4.03    inference(definition_unfolding,[],[f23,f17,f21])).
% 27.95/4.03  
% 27.95/4.03  cnf(c_47,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_390,plain,
% 27.95/4.03      ( X0 != X1
% 27.95/4.03      | X0 = k2_xboole_0(sK0,sK1)
% 27.95/4.03      | k2_xboole_0(sK0,sK1) != X1 ),
% 27.95/4.03      inference(instantiation,[status(thm)],[c_47]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_10529,plain,
% 27.95/4.03      ( X0 != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
% 27.95/4.03      | X0 = k2_xboole_0(sK0,sK1)
% 27.95/4.03      | k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
% 27.95/4.03      inference(instantiation,[status(thm)],[c_390]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_114096,plain,
% 27.95/4.03      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
% 27.95/4.03      | k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) = k2_xboole_0(sK0,sK1)
% 27.95/4.03      | k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
% 27.95/4.03      inference(instantiation,[status(thm)],[c_10529]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_2,plain,
% 27.95/4.03      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 27.95/4.03      inference(cnf_transformation,[],[f19]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_27006,plain,
% 27.95/4.03      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
% 27.95/4.03      inference(instantiation,[status(thm)],[c_2]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_1,plain,
% 27.95/4.03      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
% 27.95/4.03      inference(cnf_transformation,[],[f25]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_102,plain,
% 27.95/4.03      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = iProver_top ),
% 27.95/4.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_4,plain,
% 27.95/4.03      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 27.95/4.03      inference(cnf_transformation,[],[f22]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_101,plain,
% 27.95/4.03      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 27.95/4.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_300,plain,
% 27.95/4.03      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 27.95/4.03      inference(superposition,[status(thm)],[c_102,c_101]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_0,plain,
% 27.95/4.03      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 27.95/4.03      inference(cnf_transformation,[],[f16]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_6,negated_conjecture,
% 27.95/4.03      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
% 27.95/4.03      inference(cnf_transformation,[],[f27]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_406,plain,
% 27.95/4.03      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 27.95/4.03      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_10815,plain,
% 27.95/4.03      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 27.95/4.03      inference(superposition,[status(thm)],[c_300,c_406]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_2938,plain,
% 27.95/4.03      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 27.95/4.03      inference(instantiation,[status(thm)],[c_0]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_142,plain,
% 27.95/4.03      ( X0 != X1
% 27.95/4.03      | k2_xboole_0(sK0,sK1) != X1
% 27.95/4.03      | k2_xboole_0(sK0,sK1) = X0 ),
% 27.95/4.03      inference(instantiation,[status(thm)],[c_47]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_1049,plain,
% 27.95/4.03      ( X0 != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
% 27.95/4.03      | k2_xboole_0(sK0,sK1) = X0
% 27.95/4.03      | k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 27.95/4.03      inference(instantiation,[status(thm)],[c_142]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_2937,plain,
% 27.95/4.03      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
% 27.95/4.03      | k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
% 27.95/4.03      | k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 27.95/4.03      inference(instantiation,[status(thm)],[c_1049]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_5,plain,
% 27.95/4.03      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 27.95/4.03      inference(cnf_transformation,[],[f26]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_388,plain,
% 27.95/4.03      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k2_xboole_0(sK0,sK1) ),
% 27.95/4.03      inference(instantiation,[status(thm)],[c_5]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_205,plain,
% 27.95/4.03      ( X0 != k2_xboole_0(sK0,sK1)
% 27.95/4.03      | k2_xboole_0(sK0,sK1) = X0
% 27.95/4.03      | k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
% 27.95/4.03      inference(instantiation,[status(thm)],[c_142]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_387,plain,
% 27.95/4.03      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1)
% 27.95/4.03      | k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
% 27.95/4.03      | k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
% 27.95/4.03      inference(instantiation,[status(thm)],[c_205]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_46,plain,( X0 = X0 ),theory(equality) ).
% 27.95/4.03  
% 27.95/4.03  cnf(c_141,plain,
% 27.95/4.03      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK1) ),
% 27.95/4.03      inference(instantiation,[status(thm)],[c_46]) ).
% 27.95/4.03  
% 27.95/4.03  cnf(contradiction,plain,
% 27.95/4.03      ( $false ),
% 27.95/4.03      inference(minisat,
% 27.95/4.03                [status(thm)],
% 27.95/4.03                [c_114096,c_27006,c_10815,c_2938,c_2937,c_388,c_387,
% 27.95/4.03                 c_141]) ).
% 27.95/4.03  
% 27.95/4.03  
% 27.95/4.03  % SZS output end CNFRefutation for theBenchmark.p
% 27.95/4.03  
% 27.95/4.03  ------                               Statistics
% 27.95/4.03  
% 27.95/4.03  ------ Selected
% 27.95/4.03  
% 27.95/4.03  total_time:                             3.337
% 27.95/4.03  
%------------------------------------------------------------------------------
