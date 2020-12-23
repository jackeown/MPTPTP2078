%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:49 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 185 expanded)
%              Number of clauses        :   40 (  73 expanded)
%              Number of leaves         :    7 (  29 expanded)
%              Depth                    :   19
%              Number of atoms          :  144 ( 487 expanded)
%              Number of equality atoms :   60 ( 148 expanded)
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

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).

fof(f27,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_296,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_299,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_302,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_300,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_587,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_302,c_300])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_303,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1042,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_587,c_303])).

cnf(c_2353,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_299,c_1042])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_25,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6666,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2353,c_25])).

cnf(c_6675,plain,
    ( k2_xboole_0(sK1,sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_296,c_6666])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_301,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_929,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X3),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_301,c_300])).

cnf(c_2504,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_302,c_929])).

cnf(c_2549,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = X1
    | r1_tarski(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2504,c_303])).

cnf(c_7041,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) = sK1
    | r1_tarski(k2_xboole_0(X0,sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6675,c_2549])).

cnf(c_7053,plain,
    ( k2_xboole_0(X0,sK1) = sK1
    | r1_tarski(k2_xboole_0(X0,sK1),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7041,c_6675])).

cnf(c_8206,plain,
    ( k2_xboole_0(X0,sK1) = sK1
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_299,c_7053])).

cnf(c_2331,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2336,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2331])).

cnf(c_13154,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | k2_xboole_0(X0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8206,c_2336])).

cnf(c_13155,plain,
    ( k2_xboole_0(X0,sK1) = sK1
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_13154])).

cnf(c_13164,plain,
    ( k2_xboole_0(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_296,c_13155])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_295,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_298,plain,
    ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_924,plain,
    ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_295,c_298])).

cnf(c_1291,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_924,c_587])).

cnf(c_13643,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13164,c_1291])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_12,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13643,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.73/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.00  
% 3.73/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/1.00  
% 3.73/1.00  ------  iProver source info
% 3.73/1.00  
% 3.73/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.73/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/1.00  git: non_committed_changes: false
% 3.73/1.00  git: last_make_outside_of_git: false
% 3.73/1.00  
% 3.73/1.00  ------ 
% 3.73/1.00  ------ Parsing...
% 3.73/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  ------ Proving...
% 3.73/1.00  ------ Problem Properties 
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  clauses                                 9
% 3.73/1.00  conjectures                             3
% 3.73/1.00  EPR                                     4
% 3.73/1.00  Horn                                    9
% 3.73/1.00  unary                                   4
% 3.73/1.00  binary                                  3
% 3.73/1.00  lits                                    16
% 3.73/1.00  lits eq                                 2
% 3.73/1.00  fd_pure                                 0
% 3.73/1.00  fd_pseudo                               0
% 3.73/1.00  fd_cond                                 0
% 3.73/1.00  fd_pseudo_cond                          1
% 3.73/1.00  AC symbols                              0
% 3.73/1.00  
% 3.73/1.00  ------ Input Options Time Limit: Unbounded
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ 
% 3.73/1.00  Current options:
% 3.73/1.00  ------ 
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  % SZS status Theorem for theBenchmark.p
% 3.73/1.00  
% 3.73/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/1.00  
% 3.73/1.00  fof(f6,conjecture,(
% 3.73/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f7,negated_conjecture,(
% 3.73/1.00    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 3.73/1.00    inference(negated_conjecture,[],[f6])).
% 3.73/1.00  
% 3.73/1.00  fof(f13,plain,(
% 3.73/1.00    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 3.73/1.00    inference(ennf_transformation,[],[f7])).
% 3.73/1.00  
% 3.73/1.00  fof(f14,plain,(
% 3.73/1.00    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 3.73/1.00    inference(flattening,[],[f13])).
% 3.73/1.00  
% 3.73/1.00  fof(f17,plain,(
% 3.73/1.00    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 3.73/1.00    introduced(choice_axiom,[])).
% 3.73/1.00  
% 3.73/1.00  fof(f18,plain,(
% 3.73/1.00    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 3.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).
% 3.73/1.00  
% 3.73/1.00  fof(f27,plain,(
% 3.73/1.00    r1_tarski(sK0,sK1)),
% 3.73/1.00    inference(cnf_transformation,[],[f18])).
% 3.73/1.00  
% 3.73/1.00  fof(f4,axiom,(
% 3.73/1.00    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f10,plain,(
% 3.73/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.73/1.00    inference(ennf_transformation,[],[f4])).
% 3.73/1.00  
% 3.73/1.00  fof(f11,plain,(
% 3.73/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.73/1.00    inference(flattening,[],[f10])).
% 3.73/1.00  
% 3.73/1.00  fof(f24,plain,(
% 3.73/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f11])).
% 3.73/1.00  
% 3.73/1.00  fof(f1,axiom,(
% 3.73/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f15,plain,(
% 3.73/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.73/1.00    inference(nnf_transformation,[],[f1])).
% 3.73/1.00  
% 3.73/1.00  fof(f16,plain,(
% 3.73/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.73/1.00    inference(flattening,[],[f15])).
% 3.73/1.00  
% 3.73/1.00  fof(f20,plain,(
% 3.73/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.73/1.00    inference(cnf_transformation,[],[f16])).
% 3.73/1.00  
% 3.73/1.00  fof(f29,plain,(
% 3.73/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.73/1.00    inference(equality_resolution,[],[f20])).
% 3.73/1.00  
% 3.73/1.00  fof(f3,axiom,(
% 3.73/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f9,plain,(
% 3.73/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.73/1.00    inference(ennf_transformation,[],[f3])).
% 3.73/1.00  
% 3.73/1.00  fof(f23,plain,(
% 3.73/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f9])).
% 3.73/1.00  
% 3.73/1.00  fof(f21,plain,(
% 3.73/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f16])).
% 3.73/1.00  
% 3.73/1.00  fof(f19,plain,(
% 3.73/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.73/1.00    inference(cnf_transformation,[],[f16])).
% 3.73/1.00  
% 3.73/1.00  fof(f30,plain,(
% 3.73/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.73/1.00    inference(equality_resolution,[],[f19])).
% 3.73/1.00  
% 3.73/1.00  fof(f2,axiom,(
% 3.73/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f8,plain,(
% 3.73/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.73/1.00    inference(ennf_transformation,[],[f2])).
% 3.73/1.00  
% 3.73/1.00  fof(f22,plain,(
% 3.73/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f8])).
% 3.73/1.00  
% 3.73/1.00  fof(f26,plain,(
% 3.73/1.00    v1_relat_1(sK2)),
% 3.73/1.00    inference(cnf_transformation,[],[f18])).
% 3.73/1.00  
% 3.73/1.00  fof(f5,axiom,(
% 3.73/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f12,plain,(
% 3.73/1.00    ! [X0,X1,X2] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 3.73/1.00    inference(ennf_transformation,[],[f5])).
% 3.73/1.00  
% 3.73/1.00  fof(f25,plain,(
% 3.73/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f12])).
% 3.73/1.00  
% 3.73/1.00  fof(f28,plain,(
% 3.73/1.00    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 3.73/1.00    inference(cnf_transformation,[],[f18])).
% 3.73/1.00  
% 3.73/1.00  cnf(c_8,negated_conjecture,
% 3.73/1.00      ( r1_tarski(sK0,sK1) ),
% 3.73/1.00      inference(cnf_transformation,[],[f27]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_296,plain,
% 3.73/1.00      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_5,plain,
% 3.73/1.00      ( ~ r1_tarski(X0,X1)
% 3.73/1.00      | ~ r1_tarski(X2,X1)
% 3.73/1.00      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 3.73/1.00      inference(cnf_transformation,[],[f24]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_299,plain,
% 3.73/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.73/1.00      | r1_tarski(X2,X1) != iProver_top
% 3.73/1.00      | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1,plain,
% 3.73/1.00      ( r1_tarski(X0,X0) ),
% 3.73/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_302,plain,
% 3.73/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4,plain,
% 3.73/1.00      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 3.73/1.00      inference(cnf_transformation,[],[f23]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_300,plain,
% 3.73/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.73/1.00      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_587,plain,
% 3.73/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_302,c_300]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_0,plain,
% 3.73/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.73/1.00      inference(cnf_transformation,[],[f21]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_303,plain,
% 3.73/1.00      ( X0 = X1
% 3.73/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.73/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1042,plain,
% 3.73/1.00      ( k2_xboole_0(X0,X1) = X0
% 3.73/1.00      | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_587,c_303]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_2353,plain,
% 3.73/1.00      ( k2_xboole_0(X0,X1) = X0
% 3.73/1.00      | r1_tarski(X0,X0) != iProver_top
% 3.73/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_299,c_1042]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_2,plain,
% 3.73/1.00      ( r1_tarski(X0,X0) ),
% 3.73/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_25,plain,
% 3.73/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6666,plain,
% 3.73/1.00      ( k2_xboole_0(X0,X1) = X0 | r1_tarski(X1,X0) != iProver_top ),
% 3.73/1.00      inference(global_propositional_subsumption,
% 3.73/1.00                [status(thm)],
% 3.73/1.00                [c_2353,c_25]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6675,plain,
% 3.73/1.00      ( k2_xboole_0(sK1,sK0) = sK1 ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_296,c_6666]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3,plain,
% 3.73/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 3.73/1.00      inference(cnf_transformation,[],[f22]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_301,plain,
% 3.73/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.73/1.00      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_929,plain,
% 3.73/1.00      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 3.73/1.00      | r1_tarski(k2_xboole_0(X0,X3),X2) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_301,c_300]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_2504,plain,
% 3.73/1.00      ( r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_302,c_929]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_2549,plain,
% 3.73/1.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = X1
% 3.73/1.00      | r1_tarski(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_2504,c_303]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_7041,plain,
% 3.73/1.00      ( k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) = sK1
% 3.73/1.00      | r1_tarski(k2_xboole_0(X0,sK1),sK1) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_6675,c_2549]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_7053,plain,
% 3.73/1.00      ( k2_xboole_0(X0,sK1) = sK1
% 3.73/1.00      | r1_tarski(k2_xboole_0(X0,sK1),sK1) != iProver_top ),
% 3.73/1.00      inference(light_normalisation,[status(thm)],[c_7041,c_6675]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_8206,plain,
% 3.73/1.00      ( k2_xboole_0(X0,sK1) = sK1
% 3.73/1.00      | r1_tarski(X0,sK1) != iProver_top
% 3.73/1.00      | r1_tarski(sK1,sK1) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_299,c_7053]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_2331,plain,
% 3.73/1.00      ( r1_tarski(sK1,sK1) ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_2336,plain,
% 3.73/1.00      ( r1_tarski(sK1,sK1) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_2331]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_13154,plain,
% 3.73/1.00      ( r1_tarski(X0,sK1) != iProver_top | k2_xboole_0(X0,sK1) = sK1 ),
% 3.73/1.00      inference(global_propositional_subsumption,
% 3.73/1.00                [status(thm)],
% 3.73/1.00                [c_8206,c_2336]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_13155,plain,
% 3.73/1.00      ( k2_xboole_0(X0,sK1) = sK1 | r1_tarski(X0,sK1) != iProver_top ),
% 3.73/1.00      inference(renaming,[status(thm)],[c_13154]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_13164,plain,
% 3.73/1.00      ( k2_xboole_0(sK0,sK1) = sK1 ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_296,c_13155]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_9,negated_conjecture,
% 3.73/1.00      ( v1_relat_1(sK2) ),
% 3.73/1.00      inference(cnf_transformation,[],[f26]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_295,plain,
% 3.73/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6,plain,
% 3.73/1.00      ( ~ v1_relat_1(X0)
% 3.73/1.00      | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 3.73/1.00      inference(cnf_transformation,[],[f25]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_298,plain,
% 3.73/1.00      ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
% 3.73/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_924,plain,
% 3.73/1.00      ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_295,c_298]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1291,plain,
% 3.73/1.00      ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X0,X1))) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_924,c_587]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_13643,plain,
% 3.73/1.00      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_13164,c_1291]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_7,negated_conjecture,
% 3.73/1.00      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 3.73/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_12,plain,
% 3.73/1.00      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(contradiction,plain,
% 3.73/1.00      ( $false ),
% 3.73/1.00      inference(minisat,[status(thm)],[c_13643,c_12]) ).
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/1.00  
% 3.73/1.00  ------                               Statistics
% 3.73/1.00  
% 3.73/1.00  ------ Selected
% 3.73/1.00  
% 3.73/1.00  total_time:                             0.406
% 3.73/1.00  
%------------------------------------------------------------------------------
