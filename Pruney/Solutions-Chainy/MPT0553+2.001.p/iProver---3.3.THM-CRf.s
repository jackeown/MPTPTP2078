%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:46:41 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   53 (  91 expanded)
%              Number of clauses        :   26 (  33 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :   75 ( 134 expanded)
%              Number of equality atoms :   33 (  59 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k3_tarski(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f21,f19,f19])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f16,f20,f19])).

fof(f23,plain,(
    ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) ),
    inference(definition_unfolding,[],[f15,f19,f19,f20])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f17,f19])).

cnf(c_6,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_56,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_174,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k3_tarski(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_58,plain,
    ( ~ v1_relat_1(X0_37)
    | k3_tarski(k2_tarski(k9_relat_1(X0_37,X0_38),k9_relat_1(X0_37,X1_38))) = k9_relat_1(X0_37,k3_tarski(k2_tarski(X0_38,X1_38))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_172,plain,
    ( k3_tarski(k2_tarski(k9_relat_1(X0_37,X0_38),k9_relat_1(X0_37,X1_38))) = k9_relat_1(X0_37,k3_tarski(k2_tarski(X0_38,X1_38)))
    | v1_relat_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_1297,plain,
    ( k3_tarski(k2_tarski(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,X1_38))) = k9_relat_1(sK2,k3_tarski(k2_tarski(X0_38,X1_38))) ),
    inference(superposition,[status(thm)],[c_174,c_172])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_61,plain,
    ( ~ r1_tarski(X0_38,k3_tarski(k2_tarski(X1_38,X2_38)))
    | r1_tarski(k6_subset_1(X0_38,X1_38),X2_38) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_170,plain,
    ( r1_tarski(X0_38,k3_tarski(k2_tarski(X1_38,X2_38))) != iProver_top
    | r1_tarski(k6_subset_1(X0_38,X1_38),X2_38) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_1806,plain,
    ( r1_tarski(X0_38,k9_relat_1(sK2,k3_tarski(k2_tarski(X1_38,X2_38)))) != iProver_top
    | r1_tarski(k6_subset_1(X0_38,k9_relat_1(sK2,X1_38)),k9_relat_1(sK2,X2_38)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_170])).

cnf(c_5,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_57,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_173,plain,
    ( r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_5837,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1806,c_173])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_62,plain,
    ( k3_tarski(k2_tarski(X0_38,k6_subset_1(X1_38,X0_38))) = k3_tarski(k2_tarski(X0_38,X1_38)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_5839,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k3_tarski(k2_tarski(sK1,sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5837,c_62])).

cnf(c_3,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_59,plain,
    ( k2_tarski(X0_38,X1_38) = k2_tarski(X1_38,X0_38) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_60,plain,
    ( r1_tarski(X0_38,k3_tarski(k2_tarski(X0_38,X1_38))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_171,plain,
    ( r1_tarski(X0_38,k3_tarski(k2_tarski(X0_38,X1_38))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_286,plain,
    ( r1_tarski(X0_38,k3_tarski(k2_tarski(X1_38,X0_38))) = iProver_top ),
    inference(superposition,[status(thm)],[c_59,c_171])).

cnf(c_1818,plain,
    ( r1_tarski(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,k3_tarski(k2_tarski(X1_38,X0_38)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_286])).

cnf(c_5872,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5839,c_1818])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:49:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.64/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.64/0.99  
% 3.64/0.99  ------  iProver source info
% 3.64/0.99  
% 3.64/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.64/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.64/0.99  git: non_committed_changes: false
% 3.64/0.99  git: last_make_outside_of_git: false
% 3.64/0.99  
% 3.64/0.99  ------ 
% 3.64/0.99  ------ Parsing...
% 3.64/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/0.99  ------ Proving...
% 3.64/0.99  ------ Problem Properties 
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  clauses                                 7
% 3.64/0.99  conjectures                             2
% 3.64/0.99  EPR                                     1
% 3.64/0.99  Horn                                    7
% 3.64/0.99  unary                                   5
% 3.64/0.99  binary                                  2
% 3.64/0.99  lits                                    9
% 3.64/0.99  lits eq                                 3
% 3.64/0.99  fd_pure                                 0
% 3.64/0.99  fd_pseudo                               0
% 3.64/0.99  fd_cond                                 0
% 3.64/0.99  fd_pseudo_cond                          0
% 3.64/0.99  AC symbols                              0
% 3.64/0.99  
% 3.64/0.99  ------ Input Options Time Limit: Unbounded
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ 
% 3.64/0.99  Current options:
% 3.64/0.99  ------ 
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ Proving...
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  % SZS status Theorem for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99   Resolution empty clause
% 3.64/0.99  
% 3.64/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  fof(f8,conjecture,(
% 3.64/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f9,negated_conjecture,(
% 3.64/0.99    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 3.64/0.99    inference(negated_conjecture,[],[f8])).
% 3.64/0.99  
% 3.64/0.99  fof(f12,plain,(
% 3.64/0.99    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2))),
% 3.64/0.99    inference(ennf_transformation,[],[f9])).
% 3.64/0.99  
% 3.64/0.99  fof(f13,plain,(
% 3.64/0.99    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2)) => (~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2))),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f14,plain,(
% 3.64/0.99    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2)),
% 3.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 3.64/0.99  
% 3.64/0.99  fof(f22,plain,(
% 3.64/0.99    v1_relat_1(sK2)),
% 3.64/0.99    inference(cnf_transformation,[],[f14])).
% 3.64/0.99  
% 3.64/0.99  fof(f7,axiom,(
% 3.64/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f11,plain,(
% 3.64/0.99    ! [X0,X1,X2] : (k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 3.64/0.99    inference(ennf_transformation,[],[f7])).
% 3.64/0.99  
% 3.64/0.99  fof(f21,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f11])).
% 3.64/0.99  
% 3.64/0.99  fof(f5,axiom,(
% 3.64/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f19,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.64/0.99    inference(cnf_transformation,[],[f5])).
% 3.64/0.99  
% 3.64/0.99  fof(f27,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k3_tarski(k2_tarski(X0,X1))) | ~v1_relat_1(X2)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f21,f19,f19])).
% 3.64/0.99  
% 3.64/0.99  fof(f2,axiom,(
% 3.64/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f10,plain,(
% 3.64/0.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.64/0.99    inference(ennf_transformation,[],[f2])).
% 3.64/0.99  
% 3.64/0.99  fof(f16,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.64/0.99    inference(cnf_transformation,[],[f10])).
% 3.64/0.99  
% 3.64/0.99  fof(f6,axiom,(
% 3.64/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f20,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f6])).
% 3.64/0.99  
% 3.64/0.99  fof(f25,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 3.64/0.99    inference(definition_unfolding,[],[f16,f20,f19])).
% 3.64/0.99  
% 3.64/0.99  fof(f23,plain,(
% 3.64/0.99    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 3.64/0.99    inference(cnf_transformation,[],[f14])).
% 3.64/0.99  
% 3.64/0.99  fof(f1,axiom,(
% 3.64/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f15,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.64/0.99    inference(cnf_transformation,[],[f1])).
% 3.64/0.99  
% 3.64/0.99  fof(f24,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0)))) )),
% 3.64/0.99    inference(definition_unfolding,[],[f15,f19,f19,f20])).
% 3.64/0.99  
% 3.64/0.99  fof(f4,axiom,(
% 3.64/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f18,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f4])).
% 3.64/0.99  
% 3.64/0.99  fof(f3,axiom,(
% 3.64/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f17,plain,(
% 3.64/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.64/0.99    inference(cnf_transformation,[],[f3])).
% 3.64/0.99  
% 3.64/0.99  fof(f26,plain,(
% 3.64/0.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 3.64/0.99    inference(definition_unfolding,[],[f17,f19])).
% 3.64/0.99  
% 3.64/0.99  cnf(c_6,negated_conjecture,
% 3.64/0.99      ( v1_relat_1(sK2) ),
% 3.64/0.99      inference(cnf_transformation,[],[f22]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_56,negated_conjecture,
% 3.64/0.99      ( v1_relat_1(sK2) ),
% 3.64/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_174,plain,
% 3.64/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_4,plain,
% 3.64/0.99      ( ~ v1_relat_1(X0)
% 3.64/0.99      | k3_tarski(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k3_tarski(k2_tarski(X1,X2))) ),
% 3.64/0.99      inference(cnf_transformation,[],[f27]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_58,plain,
% 3.64/0.99      ( ~ v1_relat_1(X0_37)
% 3.64/0.99      | k3_tarski(k2_tarski(k9_relat_1(X0_37,X0_38),k9_relat_1(X0_37,X1_38))) = k9_relat_1(X0_37,k3_tarski(k2_tarski(X0_38,X1_38))) ),
% 3.64/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_172,plain,
% 3.64/0.99      ( k3_tarski(k2_tarski(k9_relat_1(X0_37,X0_38),k9_relat_1(X0_37,X1_38))) = k9_relat_1(X0_37,k3_tarski(k2_tarski(X0_38,X1_38)))
% 3.64/0.99      | v1_relat_1(X0_37) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1297,plain,
% 3.64/0.99      ( k3_tarski(k2_tarski(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,X1_38))) = k9_relat_1(sK2,k3_tarski(k2_tarski(X0_38,X1_38))) ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_174,c_172]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1,plain,
% 3.64/0.99      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
% 3.64/0.99      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 3.64/0.99      inference(cnf_transformation,[],[f25]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_61,plain,
% 3.64/0.99      ( ~ r1_tarski(X0_38,k3_tarski(k2_tarski(X1_38,X2_38)))
% 3.64/0.99      | r1_tarski(k6_subset_1(X0_38,X1_38),X2_38) ),
% 3.64/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_170,plain,
% 3.64/0.99      ( r1_tarski(X0_38,k3_tarski(k2_tarski(X1_38,X2_38))) != iProver_top
% 3.64/0.99      | r1_tarski(k6_subset_1(X0_38,X1_38),X2_38) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1806,plain,
% 3.64/0.99      ( r1_tarski(X0_38,k9_relat_1(sK2,k3_tarski(k2_tarski(X1_38,X2_38)))) != iProver_top
% 3.64/0.99      | r1_tarski(k6_subset_1(X0_38,k9_relat_1(sK2,X1_38)),k9_relat_1(sK2,X2_38)) = iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1297,c_170]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5,negated_conjecture,
% 3.64/0.99      ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
% 3.64/0.99      inference(cnf_transformation,[],[f23]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_57,negated_conjecture,
% 3.64/0.99      ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
% 3.64/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_173,plain,
% 3.64/0.99      ( r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5837,plain,
% 3.64/0.99      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1806,c_173]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_0,plain,
% 3.64/0.99      ( k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 3.64/0.99      inference(cnf_transformation,[],[f24]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_62,plain,
% 3.64/0.99      ( k3_tarski(k2_tarski(X0_38,k6_subset_1(X1_38,X0_38))) = k3_tarski(k2_tarski(X0_38,X1_38)) ),
% 3.64/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5839,plain,
% 3.64/0.99      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k3_tarski(k2_tarski(sK1,sK0)))) != iProver_top ),
% 3.64/0.99      inference(demodulation,[status(thm)],[c_5837,c_62]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3,plain,
% 3.64/0.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f18]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_59,plain,
% 3.64/0.99      ( k2_tarski(X0_38,X1_38) = k2_tarski(X1_38,X0_38) ),
% 3.64/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2,plain,
% 3.64/0.99      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 3.64/0.99      inference(cnf_transformation,[],[f26]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_60,plain,
% 3.64/0.99      ( r1_tarski(X0_38,k3_tarski(k2_tarski(X0_38,X1_38))) ),
% 3.64/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_171,plain,
% 3.64/0.99      ( r1_tarski(X0_38,k3_tarski(k2_tarski(X0_38,X1_38))) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_286,plain,
% 3.64/0.99      ( r1_tarski(X0_38,k3_tarski(k2_tarski(X1_38,X0_38))) = iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_59,c_171]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1818,plain,
% 3.64/0.99      ( r1_tarski(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,k3_tarski(k2_tarski(X1_38,X0_38)))) = iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1297,c_286]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5872,plain,
% 3.64/0.99      ( $false ),
% 3.64/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5839,c_1818]) ).
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  ------                               Statistics
% 3.64/0.99  
% 3.64/0.99  ------ Selected
% 3.64/0.99  
% 3.64/0.99  total_time:                             0.19
% 3.64/0.99  
%------------------------------------------------------------------------------
