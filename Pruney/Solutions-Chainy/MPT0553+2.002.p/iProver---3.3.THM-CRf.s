%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:46:41 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   49 (  72 expanded)
%              Number of clauses        :   26 (  33 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :   12
%              Number of atoms          :   70 ( 113 expanded)
%              Number of equality atoms :   30 (  41 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f16,f18])).

fof(f21,plain,(
    ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f15,f18])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_6,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_55,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_168,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_57,plain,
    ( ~ v1_relat_1(X0_36)
    | k2_xboole_0(k9_relat_1(X0_36,X0_37),k9_relat_1(X0_36,X1_37)) = k9_relat_1(X0_36,k2_xboole_0(X0_37,X1_37)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_166,plain,
    ( k2_xboole_0(k9_relat_1(X0_36,X0_37),k9_relat_1(X0_36,X1_37)) = k9_relat_1(X0_36,k2_xboole_0(X0_37,X1_37))
    | v1_relat_1(X0_36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_1403,plain,
    ( k2_xboole_0(k9_relat_1(sK2,X0_37),k9_relat_1(sK2,X1_37)) = k9_relat_1(sK2,k2_xboole_0(X0_37,X1_37)) ),
    inference(superposition,[status(thm)],[c_168,c_166])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_59,plain,
    ( ~ r1_tarski(X0_37,k2_xboole_0(X1_37,X2_37))
    | r1_tarski(k6_subset_1(X0_37,X1_37),X2_37) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_164,plain,
    ( r1_tarski(X0_37,k2_xboole_0(X1_37,X2_37)) != iProver_top
    | r1_tarski(k6_subset_1(X0_37,X1_37),X2_37) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_1993,plain,
    ( r1_tarski(X0_37,k9_relat_1(sK2,k2_xboole_0(X1_37,X2_37))) != iProver_top
    | r1_tarski(k6_subset_1(X0_37,k9_relat_1(sK2,X1_37)),k9_relat_1(sK2,X2_37)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_164])).

cnf(c_5,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_56,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_167,plain,
    ( r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_11387,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1993,c_167])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_60,plain,
    ( k2_xboole_0(X0_37,k6_subset_1(X1_37,X0_37)) = k2_xboole_0(X0_37,X1_37) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_11389,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11387,c_60])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_61,plain,
    ( k2_xboole_0(X0_37,X1_37) = k2_xboole_0(X1_37,X0_37) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_58,plain,
    ( r1_tarski(X0_37,k2_xboole_0(X0_37,X1_37)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_165,plain,
    ( r1_tarski(X0_37,k2_xboole_0(X0_37,X1_37)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_275,plain,
    ( r1_tarski(X0_37,k2_xboole_0(X1_37,X0_37)) = iProver_top ),
    inference(superposition,[status(thm)],[c_61,c_165])).

cnf(c_2006,plain,
    ( r1_tarski(k9_relat_1(sK2,X0_37),k9_relat_1(sK2,k2_xboole_0(X1_37,X0_37))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_275])).

cnf(c_11848,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11389,c_2006])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.89/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.00  
% 3.89/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.89/1.00  
% 3.89/1.00  ------  iProver source info
% 3.89/1.00  
% 3.89/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.89/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.89/1.00  git: non_committed_changes: false
% 3.89/1.00  git: last_make_outside_of_git: false
% 3.89/1.00  
% 3.89/1.00  ------ 
% 3.89/1.00  ------ Parsing...
% 3.89/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.89/1.00  
% 3.89/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.89/1.00  
% 3.89/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.89/1.00  
% 3.89/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/1.00  ------ Proving...
% 3.89/1.00  ------ Problem Properties 
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  clauses                                 7
% 3.89/1.00  conjectures                             2
% 3.89/1.00  EPR                                     1
% 3.89/1.00  Horn                                    7
% 3.89/1.00  unary                                   5
% 3.89/1.00  binary                                  2
% 3.89/1.00  lits                                    9
% 3.89/1.00  lits eq                                 3
% 3.89/1.00  fd_pure                                 0
% 3.89/1.00  fd_pseudo                               0
% 3.89/1.00  fd_cond                                 0
% 3.89/1.00  fd_pseudo_cond                          0
% 3.89/1.00  AC symbols                              0
% 3.89/1.00  
% 3.89/1.00  ------ Input Options Time Limit: Unbounded
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  ------ 
% 3.89/1.00  Current options:
% 3.89/1.00  ------ 
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  ------ Proving...
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  % SZS status Theorem for theBenchmark.p
% 3.89/1.00  
% 3.89/1.00   Resolution empty clause
% 3.89/1.00  
% 3.89/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.89/1.00  
% 3.89/1.00  fof(f7,conjecture,(
% 3.89/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 3.89/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f8,negated_conjecture,(
% 3.89/1.00    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 3.89/1.00    inference(negated_conjecture,[],[f7])).
% 3.89/1.00  
% 3.89/1.00  fof(f11,plain,(
% 3.89/1.00    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2))),
% 3.89/1.00    inference(ennf_transformation,[],[f8])).
% 3.89/1.00  
% 3.89/1.00  fof(f12,plain,(
% 3.89/1.00    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2)) => (~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2))),
% 3.89/1.00    introduced(choice_axiom,[])).
% 3.89/1.00  
% 3.89/1.00  fof(f13,plain,(
% 3.89/1.00    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2)),
% 3.89/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 3.89/1.00  
% 3.89/1.00  fof(f20,plain,(
% 3.89/1.00    v1_relat_1(sK2)),
% 3.89/1.00    inference(cnf_transformation,[],[f13])).
% 3.89/1.00  
% 3.89/1.00  fof(f6,axiom,(
% 3.89/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)))),
% 3.89/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f10,plain,(
% 3.89/1.00    ! [X0,X1,X2] : (k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 3.89/1.00    inference(ennf_transformation,[],[f6])).
% 3.89/1.00  
% 3.89/1.00  fof(f19,plain,(
% 3.89/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f10])).
% 3.89/1.00  
% 3.89/1.00  fof(f3,axiom,(
% 3.89/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.89/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f9,plain,(
% 3.89/1.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.89/1.00    inference(ennf_transformation,[],[f3])).
% 3.89/1.00  
% 3.89/1.00  fof(f16,plain,(
% 3.89/1.00    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.89/1.00    inference(cnf_transformation,[],[f9])).
% 3.89/1.00  
% 3.89/1.00  fof(f5,axiom,(
% 3.89/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.89/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f18,plain,(
% 3.89/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f5])).
% 3.89/1.00  
% 3.89/1.00  fof(f23,plain,(
% 3.89/1.00    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.89/1.00    inference(definition_unfolding,[],[f16,f18])).
% 3.89/1.00  
% 3.89/1.00  fof(f21,plain,(
% 3.89/1.00    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 3.89/1.00    inference(cnf_transformation,[],[f13])).
% 3.89/1.00  
% 3.89/1.00  fof(f2,axiom,(
% 3.89/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.89/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f15,plain,(
% 3.89/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.89/1.00    inference(cnf_transformation,[],[f2])).
% 3.89/1.00  
% 3.89/1.00  fof(f22,plain,(
% 3.89/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 3.89/1.00    inference(definition_unfolding,[],[f15,f18])).
% 3.89/1.00  
% 3.89/1.00  fof(f1,axiom,(
% 3.89/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.89/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f14,plain,(
% 3.89/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f1])).
% 3.89/1.00  
% 3.89/1.00  fof(f4,axiom,(
% 3.89/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.89/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f17,plain,(
% 3.89/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.89/1.00    inference(cnf_transformation,[],[f4])).
% 3.89/1.00  
% 3.89/1.00  cnf(c_6,negated_conjecture,
% 3.89/1.00      ( v1_relat_1(sK2) ),
% 3.89/1.00      inference(cnf_transformation,[],[f20]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_55,negated_conjecture,
% 3.89/1.00      ( v1_relat_1(sK2) ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_168,plain,
% 3.89/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_4,plain,
% 3.89/1.00      ( ~ v1_relat_1(X0)
% 3.89/1.00      | k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 3.89/1.00      inference(cnf_transformation,[],[f19]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_57,plain,
% 3.89/1.00      ( ~ v1_relat_1(X0_36)
% 3.89/1.00      | k2_xboole_0(k9_relat_1(X0_36,X0_37),k9_relat_1(X0_36,X1_37)) = k9_relat_1(X0_36,k2_xboole_0(X0_37,X1_37)) ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_166,plain,
% 3.89/1.00      ( k2_xboole_0(k9_relat_1(X0_36,X0_37),k9_relat_1(X0_36,X1_37)) = k9_relat_1(X0_36,k2_xboole_0(X0_37,X1_37))
% 3.89/1.00      | v1_relat_1(X0_36) != iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1403,plain,
% 3.89/1.00      ( k2_xboole_0(k9_relat_1(sK2,X0_37),k9_relat_1(sK2,X1_37)) = k9_relat_1(sK2,k2_xboole_0(X0_37,X1_37)) ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_168,c_166]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_2,plain,
% 3.89/1.00      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 3.89/1.00      inference(cnf_transformation,[],[f23]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_59,plain,
% 3.89/1.00      ( ~ r1_tarski(X0_37,k2_xboole_0(X1_37,X2_37))
% 3.89/1.00      | r1_tarski(k6_subset_1(X0_37,X1_37),X2_37) ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_164,plain,
% 3.89/1.00      ( r1_tarski(X0_37,k2_xboole_0(X1_37,X2_37)) != iProver_top
% 3.89/1.00      | r1_tarski(k6_subset_1(X0_37,X1_37),X2_37) = iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1993,plain,
% 3.89/1.00      ( r1_tarski(X0_37,k9_relat_1(sK2,k2_xboole_0(X1_37,X2_37))) != iProver_top
% 3.89/1.00      | r1_tarski(k6_subset_1(X0_37,k9_relat_1(sK2,X1_37)),k9_relat_1(sK2,X2_37)) = iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_1403,c_164]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_5,negated_conjecture,
% 3.89/1.00      ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
% 3.89/1.00      inference(cnf_transformation,[],[f21]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_56,negated_conjecture,
% 3.89/1.00      ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_167,plain,
% 3.89/1.00      ( r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) != iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_11387,plain,
% 3.89/1.00      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) != iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_1993,c_167]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1,plain,
% 3.89/1.00      ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.89/1.00      inference(cnf_transformation,[],[f22]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_60,plain,
% 3.89/1.00      ( k2_xboole_0(X0_37,k6_subset_1(X1_37,X0_37)) = k2_xboole_0(X0_37,X1_37) ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_11389,plain,
% 3.89/1.00      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK1,sK0))) != iProver_top ),
% 3.89/1.00      inference(demodulation,[status(thm)],[c_11387,c_60]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_0,plain,
% 3.89/1.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.89/1.00      inference(cnf_transformation,[],[f14]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_61,plain,
% 3.89/1.00      ( k2_xboole_0(X0_37,X1_37) = k2_xboole_0(X1_37,X0_37) ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_3,plain,
% 3.89/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.89/1.00      inference(cnf_transformation,[],[f17]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_58,plain,
% 3.89/1.00      ( r1_tarski(X0_37,k2_xboole_0(X0_37,X1_37)) ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_165,plain,
% 3.89/1.00      ( r1_tarski(X0_37,k2_xboole_0(X0_37,X1_37)) = iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_275,plain,
% 3.89/1.00      ( r1_tarski(X0_37,k2_xboole_0(X1_37,X0_37)) = iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_61,c_165]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_2006,plain,
% 3.89/1.00      ( r1_tarski(k9_relat_1(sK2,X0_37),k9_relat_1(sK2,k2_xboole_0(X1_37,X0_37))) = iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_1403,c_275]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_11848,plain,
% 3.89/1.00      ( $false ),
% 3.89/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_11389,c_2006]) ).
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.89/1.00  
% 3.89/1.00  ------                               Statistics
% 3.89/1.00  
% 3.89/1.00  ------ Selected
% 3.89/1.00  
% 3.89/1.00  total_time:                             0.389
% 3.89/1.00  
%------------------------------------------------------------------------------
