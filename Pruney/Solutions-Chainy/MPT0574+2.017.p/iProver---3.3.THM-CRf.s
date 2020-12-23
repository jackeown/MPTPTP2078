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
% DateTime   : Thu Dec  3 11:47:48 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   51 (  70 expanded)
%              Number of clauses        :   25 (  27 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :   11
%              Number of atoms          :  106 ( 167 expanded)
%              Number of equality atoms :   39 (  45 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f25,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f13])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f26,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_260,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_262,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_263,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_265,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_779,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_263,c_265])).

cnf(c_1245,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_262,c_779])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_22,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6821,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1245,c_22])).

cnf(c_6828,plain,
    ( k2_xboole_0(sK1,sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_260,c_6821])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_97,plain,
    ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_98,plain,
    ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_97])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_497,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_263])).

cnf(c_636,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_98,c_497])).

cnf(c_7803,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6828,c_636])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_12,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7803,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.30/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.00  
% 3.30/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.30/1.00  
% 3.30/1.00  ------  iProver source info
% 3.30/1.00  
% 3.30/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.30/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.30/1.00  git: non_committed_changes: false
% 3.30/1.00  git: last_make_outside_of_git: false
% 3.30/1.00  
% 3.30/1.00  ------ 
% 3.30/1.00  ------ Parsing...
% 3.30/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.30/1.00  ------ Proving...
% 3.30/1.00  ------ Problem Properties 
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  clauses                                 8
% 3.30/1.00  conjectures                             2
% 3.30/1.00  EPR                                     3
% 3.30/1.00  Horn                                    8
% 3.30/1.00  unary                                   6
% 3.30/1.00  binary                                  0
% 3.30/1.00  lits                                    12
% 3.30/1.00  lits eq                                 3
% 3.30/1.00  fd_pure                                 0
% 3.30/1.00  fd_pseudo                               0
% 3.30/1.00  fd_cond                                 0
% 3.30/1.00  fd_pseudo_cond                          1
% 3.30/1.00  AC symbols                              0
% 3.30/1.00  
% 3.30/1.00  ------ Input Options Time Limit: Unbounded
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  ------ 
% 3.30/1.00  Current options:
% 3.30/1.00  ------ 
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  ------ Proving...
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  % SZS status Theorem for theBenchmark.p
% 3.30/1.00  
% 3.30/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.30/1.00  
% 3.30/1.00  fof(f6,conjecture,(
% 3.30/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f7,negated_conjecture,(
% 3.30/1.00    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 3.30/1.00    inference(negated_conjecture,[],[f6])).
% 3.30/1.00  
% 3.30/1.00  fof(f11,plain,(
% 3.30/1.00    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 3.30/1.00    inference(ennf_transformation,[],[f7])).
% 3.30/1.00  
% 3.30/1.00  fof(f12,plain,(
% 3.30/1.00    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 3.30/1.00    inference(flattening,[],[f11])).
% 3.30/1.00  
% 3.30/1.00  fof(f15,plain,(
% 3.30/1.00    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f16,plain,(
% 3.30/1.00    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 3.30/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 3.30/1.00  
% 3.30/1.00  fof(f25,plain,(
% 3.30/1.00    r1_tarski(sK0,sK1)),
% 3.30/1.00    inference(cnf_transformation,[],[f16])).
% 3.30/1.00  
% 3.30/1.00  fof(f4,axiom,(
% 3.30/1.00    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f8,plain,(
% 3.30/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.30/1.00    inference(ennf_transformation,[],[f4])).
% 3.30/1.00  
% 3.30/1.00  fof(f9,plain,(
% 3.30/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.30/1.00    inference(flattening,[],[f8])).
% 3.30/1.00  
% 3.30/1.00  fof(f22,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f9])).
% 3.30/1.00  
% 3.30/1.00  fof(f3,axiom,(
% 3.30/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f21,plain,(
% 3.30/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.30/1.00    inference(cnf_transformation,[],[f3])).
% 3.30/1.00  
% 3.30/1.00  fof(f2,axiom,(
% 3.30/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f13,plain,(
% 3.30/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.30/1.00    inference(nnf_transformation,[],[f2])).
% 3.30/1.00  
% 3.30/1.00  fof(f14,plain,(
% 3.30/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.30/1.00    inference(flattening,[],[f13])).
% 3.30/1.00  
% 3.30/1.00  fof(f20,plain,(
% 3.30/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f14])).
% 3.30/1.00  
% 3.30/1.00  fof(f18,plain,(
% 3.30/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.30/1.00    inference(cnf_transformation,[],[f14])).
% 3.30/1.00  
% 3.30/1.00  fof(f28,plain,(
% 3.30/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.30/1.00    inference(equality_resolution,[],[f18])).
% 3.30/1.00  
% 3.30/1.00  fof(f5,axiom,(
% 3.30/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f10,plain,(
% 3.30/1.00    ! [X0,X1,X2] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 3.30/1.00    inference(ennf_transformation,[],[f5])).
% 3.30/1.00  
% 3.30/1.00  fof(f23,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f10])).
% 3.30/1.00  
% 3.30/1.00  fof(f24,plain,(
% 3.30/1.00    v1_relat_1(sK2)),
% 3.30/1.00    inference(cnf_transformation,[],[f16])).
% 3.30/1.00  
% 3.30/1.00  fof(f1,axiom,(
% 3.30/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f17,plain,(
% 3.30/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f1])).
% 3.30/1.00  
% 3.30/1.00  fof(f26,plain,(
% 3.30/1.00    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 3.30/1.00    inference(cnf_transformation,[],[f16])).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8,negated_conjecture,
% 3.30/1.00      ( r1_tarski(sK0,sK1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f25]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_260,plain,
% 3.30/1.00      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_5,plain,
% 3.30/1.00      ( ~ r1_tarski(X0,X1)
% 3.30/1.00      | ~ r1_tarski(X2,X1)
% 3.30/1.00      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f22]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_262,plain,
% 3.30/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.30/1.00      | r1_tarski(X2,X1) != iProver_top
% 3.30/1.00      | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4,plain,
% 3.30/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.30/1.00      inference(cnf_transformation,[],[f21]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_263,plain,
% 3.30/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1,plain,
% 3.30/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.30/1.00      inference(cnf_transformation,[],[f20]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_265,plain,
% 3.30/1.00      ( X0 = X1
% 3.30/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.30/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_779,plain,
% 3.30/1.00      ( k2_xboole_0(X0,X1) = X0
% 3.30/1.00      | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_263,c_265]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1245,plain,
% 3.30/1.00      ( k2_xboole_0(X0,X1) = X0
% 3.30/1.00      | r1_tarski(X0,X0) != iProver_top
% 3.30/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_262,c_779]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3,plain,
% 3.30/1.00      ( r1_tarski(X0,X0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_22,plain,
% 3.30/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_6821,plain,
% 3.30/1.00      ( k2_xboole_0(X0,X1) = X0 | r1_tarski(X1,X0) != iProver_top ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_1245,c_22]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_6828,plain,
% 3.30/1.00      ( k2_xboole_0(sK1,sK0) = sK1 ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_260,c_6821]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_6,plain,
% 3.30/1.00      ( ~ v1_relat_1(X0)
% 3.30/1.00      | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 3.30/1.00      inference(cnf_transformation,[],[f23]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9,negated_conjecture,
% 3.30/1.00      ( v1_relat_1(sK2) ),
% 3.30/1.00      inference(cnf_transformation,[],[f24]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_97,plain,
% 3.30/1.00      ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
% 3.30/1.00      | sK2 != X0 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_9]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_98,plain,
% 3.30/1.00      ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_97]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_0,plain,
% 3.30/1.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f17]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_497,plain,
% 3.30/1.00      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_0,c_263]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_636,plain,
% 3.30/1.00      ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X1,X0))) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_98,c_497]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_7803,plain,
% 3.30/1.00      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_6828,c_636]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_7,negated_conjecture,
% 3.30/1.00      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 3.30/1.00      inference(cnf_transformation,[],[f26]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_12,plain,
% 3.30/1.00      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(contradiction,plain,
% 3.30/1.00      ( $false ),
% 3.30/1.00      inference(minisat,[status(thm)],[c_7803,c_12]) ).
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.30/1.00  
% 3.30/1.00  ------                               Statistics
% 3.30/1.00  
% 3.30/1.00  ------ Selected
% 3.30/1.00  
% 3.30/1.00  total_time:                             0.252
% 3.30/1.00  
%------------------------------------------------------------------------------
