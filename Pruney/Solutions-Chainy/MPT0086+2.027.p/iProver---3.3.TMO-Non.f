%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:28 EST 2020

% Result     : Timeout 59.91s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   68 ( 147 expanded)
%              Number of clauses        :   41 (  94 expanded)
%              Number of leaves         :   14 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  115 ( 256 expanded)
%              Number of equality atoms :   57 ( 158 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f22])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f9,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(ennf_transformation,[],[f10])).

fof(f15,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1)
   => ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f25,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_57,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_56,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_629,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_57,c_56])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_770,plain,
    ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_629,c_2])).

cnf(c_59,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_757,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != k4_xboole_0(X1,X3)
    | k4_xboole_0(X0,X2) = X4 ),
    inference(resolution,[status(thm)],[c_59,c_57])).

cnf(c_5398,plain,
    ( X0 != X1
    | X2 != k4_xboole_0(X1,k1_xboole_0)
    | k4_xboole_0(X0,X2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_770,c_757])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_772,plain,
    ( X0 = k4_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_629,c_3])).

cnf(c_183349,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5398,c_772])).

cnf(c_58,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_296,plain,
    ( ~ r1_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X3)))
    | r1_xboole_0(X4,k4_xboole_0(k4_xboole_0(X1,X2),X3))
    | X4 != X0 ),
    inference(resolution,[status(thm)],[c_58,c_4])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_182,plain,
    ( r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_1,c_5])).

cnf(c_3663,plain,
    ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X3))
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_296,c_182])).

cnf(c_606,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_56,c_58])).

cnf(c_781,plain,
    ( X0 = X1
    | X1 != k4_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_772,c_57])).

cnf(c_1136,plain,
    ( X0 = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_781,c_3])).

cnf(c_2008,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0),X1) ),
    inference(resolution,[status(thm)],[c_606,c_1136])).

cnf(c_292,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k4_xboole_0(X1,k1_xboole_0))
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_58,c_3])).

cnf(c_602,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_56,c_292])).

cnf(c_962,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X1,k1_xboole_0),X0) ),
    inference(resolution,[status(thm)],[c_602,c_1])).

cnf(c_4714,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2008,c_962])).

cnf(c_7502,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X2)
    | X2 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3663,c_4714])).

cnf(c_782,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0))
    | ~ r1_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
    inference(resolution,[status(thm)],[c_772,c_292])).

cnf(c_8284,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0))
    | X1 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7502,c_782])).

cnf(c_12538,plain,
    ( r1_xboole_0(X0,X1)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8284,c_4714])).

cnf(c_189967,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X2)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_183349,c_12538])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_190007,plain,
    ( r1_xboole_0(X0,X1)
    | X0 != k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_189967,c_6])).

cnf(c_3926,plain,
    ( X0 != X1
    | X2 != k2_xboole_0(X3,X4)
    | k4_xboole_0(X0,X2) = k4_xboole_0(k4_xboole_0(X1,X3),X4) ),
    inference(resolution,[status(thm)],[c_757,c_4])).

cnf(c_192036,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X2)
    | X0 != X0
    | X1 != k2_xboole_0(X1,X2) ),
    inference(resolution,[status(thm)],[c_190007,c_3926])).

cnf(c_192037,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X2)
    | X1 != k2_xboole_0(X1,X2) ),
    inference(equality_resolution_simp,[status(thm)],[c_192036])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_768,plain,
    ( X0 = k2_xboole_0(X0,X0) ),
    inference(resolution,[status(thm)],[c_629,c_0])).

cnf(c_270628,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[status(thm)],[c_192037,c_768])).

cnf(c_7,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_270650,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_270628,c_7])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 59.91/7.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 59.91/7.99  
% 59.91/7.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.91/7.99  
% 59.91/7.99  ------  iProver source info
% 59.91/7.99  
% 59.91/7.99  git: date: 2020-06-30 10:37:57 +0100
% 59.91/7.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.91/7.99  git: non_committed_changes: false
% 59.91/7.99  git: last_make_outside_of_git: false
% 59.91/7.99  
% 59.91/7.99  ------ 
% 59.91/7.99  ------ Parsing...
% 59.91/7.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  ------ Proving...
% 59.91/7.99  ------ Problem Properties 
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  clauses                                 8
% 59.91/7.99  conjectures                             1
% 59.91/7.99  EPR                                     2
% 59.91/7.99  Horn                                    8
% 59.91/7.99  unary                                   6
% 59.91/7.99  binary                                  2
% 59.91/7.99  lits                                    10
% 59.91/7.99  lits eq                                 4
% 59.91/7.99  fd_pure                                 0
% 59.91/7.99  fd_pseudo                               0
% 59.91/7.99  fd_cond                                 0
% 59.91/7.99  fd_pseudo_cond                          0
% 59.91/7.99  AC symbols                              0
% 59.91/7.99  
% 59.91/7.99  ------ Input Options Time Limit: Unbounded
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ 
% 59.91/7.99  Current options:
% 59.91/7.99  ------ 
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  % SZS status Theorem for theBenchmark.p
% 59.91/7.99  
% 59.91/7.99   Resolution empty clause
% 59.91/7.99  
% 59.91/7.99  % SZS output start CNFRefutation for theBenchmark.p
% 59.91/7.99  
% 59.91/7.99  fof(f3,axiom,(
% 59.91/7.99    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 59.91/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f19,plain,(
% 59.91/7.99    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 59.91/7.99    inference(cnf_transformation,[],[f3])).
% 59.91/7.99  
% 59.91/7.99  fof(f6,axiom,(
% 59.91/7.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 59.91/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f22,plain,(
% 59.91/7.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 59.91/7.99    inference(cnf_transformation,[],[f6])).
% 59.91/7.99  
% 59.91/7.99  fof(f26,plain,(
% 59.91/7.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 59.91/7.99    inference(definition_unfolding,[],[f19,f22])).
% 59.91/7.99  
% 59.91/7.99  fof(f4,axiom,(
% 59.91/7.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 59.91/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f20,plain,(
% 59.91/7.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 59.91/7.99    inference(cnf_transformation,[],[f4])).
% 59.91/7.99  
% 59.91/7.99  fof(f5,axiom,(
% 59.91/7.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 59.91/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f21,plain,(
% 59.91/7.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 59.91/7.99    inference(cnf_transformation,[],[f5])).
% 59.91/7.99  
% 59.91/7.99  fof(f2,axiom,(
% 59.91/7.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 59.91/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f12,plain,(
% 59.91/7.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 59.91/7.99    inference(ennf_transformation,[],[f2])).
% 59.91/7.99  
% 59.91/7.99  fof(f18,plain,(
% 59.91/7.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 59.91/7.99    inference(cnf_transformation,[],[f12])).
% 59.91/7.99  
% 59.91/7.99  fof(f7,axiom,(
% 59.91/7.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 59.91/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f23,plain,(
% 59.91/7.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 59.91/7.99    inference(cnf_transformation,[],[f7])).
% 59.91/7.99  
% 59.91/7.99  fof(f8,axiom,(
% 59.91/7.99    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 59.91/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f13,plain,(
% 59.91/7.99    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 59.91/7.99    inference(ennf_transformation,[],[f8])).
% 59.91/7.99  
% 59.91/7.99  fof(f24,plain,(
% 59.91/7.99    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 59.91/7.99    inference(cnf_transformation,[],[f13])).
% 59.91/7.99  
% 59.91/7.99  fof(f27,plain,(
% 59.91/7.99    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_xboole_0(X0,X1)) )),
% 59.91/7.99    inference(definition_unfolding,[],[f24,f22])).
% 59.91/7.99  
% 59.91/7.99  fof(f1,axiom,(
% 59.91/7.99    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 59.91/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f11,plain,(
% 59.91/7.99    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 59.91/7.99    inference(rectify,[],[f1])).
% 59.91/7.99  
% 59.91/7.99  fof(f17,plain,(
% 59.91/7.99    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 59.91/7.99    inference(cnf_transformation,[],[f11])).
% 59.91/7.99  
% 59.91/7.99  fof(f9,conjecture,(
% 59.91/7.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 59.91/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f10,negated_conjecture,(
% 59.91/7.99    ~! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 59.91/7.99    inference(negated_conjecture,[],[f9])).
% 59.91/7.99  
% 59.91/7.99  fof(f14,plain,(
% 59.91/7.99    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 59.91/7.99    inference(ennf_transformation,[],[f10])).
% 59.91/7.99  
% 59.91/7.99  fof(f15,plain,(
% 59.91/7.99    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1) => ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 59.91/7.99    introduced(choice_axiom,[])).
% 59.91/7.99  
% 59.91/7.99  fof(f16,plain,(
% 59.91/7.99    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 59.91/7.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 59.91/7.99  
% 59.91/7.99  fof(f25,plain,(
% 59.91/7.99    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 59.91/7.99    inference(cnf_transformation,[],[f16])).
% 59.91/7.99  
% 59.91/7.99  cnf(c_57,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_56,plain,( X0 = X0 ),theory(equality) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_629,plain,
% 59.91/7.99      ( X0 != X1 | X1 = X0 ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_57,c_56]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_2,plain,
% 59.91/7.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 59.91/7.99      inference(cnf_transformation,[],[f26]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_770,plain,
% 59.91/7.99      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_629,c_2]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_59,plain,
% 59.91/7.99      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 59.91/7.99      theory(equality) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_757,plain,
% 59.91/7.99      ( X0 != X1
% 59.91/7.99      | X2 != X3
% 59.91/7.99      | X4 != k4_xboole_0(X1,X3)
% 59.91/7.99      | k4_xboole_0(X0,X2) = X4 ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_59,c_57]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_5398,plain,
% 59.91/7.99      ( X0 != X1
% 59.91/7.99      | X2 != k4_xboole_0(X1,k1_xboole_0)
% 59.91/7.99      | k4_xboole_0(X0,X2) = k1_xboole_0 ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_770,c_757]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_3,plain,
% 59.91/7.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 59.91/7.99      inference(cnf_transformation,[],[f20]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_772,plain,
% 59.91/7.99      ( X0 = k4_xboole_0(X0,k1_xboole_0) ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_629,c_3]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_183349,plain,
% 59.91/7.99      ( X0 != X1 | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_5398,c_772]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_58,plain,
% 59.91/7.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 59.91/7.99      theory(equality) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_4,plain,
% 59.91/7.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 59.91/7.99      inference(cnf_transformation,[],[f21]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_296,plain,
% 59.91/7.99      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X3)))
% 59.91/7.99      | r1_xboole_0(X4,k4_xboole_0(k4_xboole_0(X1,X2),X3))
% 59.91/7.99      | X4 != X0 ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_58,c_4]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_1,plain,
% 59.91/7.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 59.91/7.99      inference(cnf_transformation,[],[f18]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_5,plain,
% 59.91/7.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 59.91/7.99      inference(cnf_transformation,[],[f23]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_182,plain,
% 59.91/7.99      ( r1_xboole_0(k1_xboole_0,X0) ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_1,c_5]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_3663,plain,
% 59.91/7.99      ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X3))
% 59.91/7.99      | X0 != k1_xboole_0 ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_296,c_182]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_606,plain,
% 59.91/7.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_56,c_58]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_781,plain,
% 59.91/7.99      ( X0 = X1 | X1 != k4_xboole_0(X0,k1_xboole_0) ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_772,c_57]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_1136,plain,
% 59.91/7.99      ( X0 = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_781,c_3]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_2008,plain,
% 59.91/7.99      ( r1_xboole_0(X0,X1)
% 59.91/7.99      | ~ r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0),X1) ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_606,c_1136]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_292,plain,
% 59.91/7.99      ( ~ r1_xboole_0(X0,X1)
% 59.91/7.99      | r1_xboole_0(X2,k4_xboole_0(X1,k1_xboole_0))
% 59.91/7.99      | X2 != X0 ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_58,c_3]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_602,plain,
% 59.91/7.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_56,c_292]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_962,plain,
% 59.91/7.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(k4_xboole_0(X1,k1_xboole_0),X0) ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_602,c_1]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_4714,plain,
% 59.91/7.99      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0)) ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_2008,c_962]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_7502,plain,
% 59.91/7.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X2) | X2 != k1_xboole_0 ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_3663,c_4714]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_782,plain,
% 59.91/7.99      ( r1_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0))
% 59.91/7.99      | ~ r1_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_772,c_292]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_8284,plain,
% 59.91/7.99      ( r1_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) | X1 != k1_xboole_0 ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_7502,c_782]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_12538,plain,
% 59.91/7.99      ( r1_xboole_0(X0,X1) | X0 != k1_xboole_0 ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_8284,c_4714]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_189967,plain,
% 59.91/7.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X2) | X0 != X1 ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_183349,c_12538]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_6,plain,
% 59.91/7.99      ( r1_xboole_0(X0,X1)
% 59.91/7.99      | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 59.91/7.99      inference(cnf_transformation,[],[f27]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_190007,plain,
% 59.91/7.99      ( r1_xboole_0(X0,X1) | X0 != k4_xboole_0(X0,X1) ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_189967,c_6]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_3926,plain,
% 59.91/7.99      ( X0 != X1
% 59.91/7.99      | X2 != k2_xboole_0(X3,X4)
% 59.91/7.99      | k4_xboole_0(X0,X2) = k4_xboole_0(k4_xboole_0(X1,X3),X4) ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_757,c_4]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_192036,plain,
% 59.91/7.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X2)
% 59.91/7.99      | X0 != X0
% 59.91/7.99      | X1 != k2_xboole_0(X1,X2) ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_190007,c_3926]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_192037,plain,
% 59.91/7.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X2) | X1 != k2_xboole_0(X1,X2) ),
% 59.91/7.99      inference(equality_resolution_simp,[status(thm)],[c_192036]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_0,plain,
% 59.91/7.99      ( k2_xboole_0(X0,X0) = X0 ),
% 59.91/7.99      inference(cnf_transformation,[],[f17]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_768,plain,
% 59.91/7.99      ( X0 = k2_xboole_0(X0,X0) ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_629,c_0]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_270628,plain,
% 59.91/7.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_192037,c_768]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_7,negated_conjecture,
% 59.91/7.99      ( ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
% 59.91/7.99      inference(cnf_transformation,[],[f25]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_270650,plain,
% 59.91/7.99      ( $false ),
% 59.91/7.99      inference(backward_subsumption_resolution,[status(thm)],[c_270628,c_7]) ).
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  % SZS output end CNFRefutation for theBenchmark.p
% 59.91/7.99  
% 59.91/7.99  ------                               Statistics
% 59.91/7.99  
% 59.91/7.99  ------ Selected
% 59.91/7.99  
% 59.91/7.99  total_time:                             7.453
% 59.91/7.99  
%------------------------------------------------------------------------------
